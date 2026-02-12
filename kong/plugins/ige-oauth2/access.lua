local url = require "socket.url"
local constants = require "kong.constants"
local timestamp = require "kong.tools.timestamp"
local secret = require "kong.plugins.ige-oauth2.secret"
local pgmoon = require "pgmoon"
local http = require "resty.http"
local cjson = require "cjson" 

local sha256_base64url = require "kong.tools.sha256".sha256_base64url

local fmt = string.format
local kong = kong
local type = type
local next = next
local table = table
local error = error
local split = require("kong.tools.string").split
local strip = require("kong.tools.string").strip
local string_find = string.find
local string_gsub = string.gsub
local string_byte = string.byte
local check_https = require("kong.tools.http").check_https
local encode_args = require("kong.tools.http").encode_args
local random_string = require("kong.tools.rand").random_string
local table_contains = require("kong.tools.table").table_contains


local ngx_decode_args = ngx.decode_args
local ngx_re_gmatch = ngx.re.gmatch
local ngx_decode_base64 = ngx.decode_base64
local ngx_encode_base64 = ngx.encode_base64


local _M = {}


local EMPTY = require("kong.tools.table").EMPTY
local SLASH = string_byte("/")
local RESPONSE_TYPE = "response_type"
local STATE = "state"
local CODE = "code"
local CODE_CHALLENGE = "code_challenge"
local CODE_CHALLENGE_METHOD = "code_challenge_method"
local CODE_VERIFIER = "code_verifier"
local CLIENT_TYPE_PUBLIC = "public"
local CLIENT_TYPE_CONFIDENTIAL = "confidential"
local TOKEN = "token"
local REFRESH_TOKEN = "refresh_token"
local SCOPE = "scope"
local CLIENT_ID = "client_id"
local CLIENT_SECRET = "client_secret"
local REDIRECT_URI = "redirect_uri"
local ACCESS_TOKEN = "access_token"
local GRANT_TYPE = "grant_type"
local GRANT_AUTHORIZATION_CODE = "authorization_code"
local GRANT_CLIENT_CREDENTIALS = "client_credentials"
local GRANT_REFRESH_TOKEN = "refresh_token"
local GRANT_PASSWORD = "password"
local ERROR = "error"
local AUTHENTICATED_USERID = "authenticated_userid"


local base64url_encode
local base64url_decode
do
  local BASE64URL_ENCODE_CHARS = "[+/]"
  local BASE64URL_ENCODE_SUBST = {
    ["+"] = "-",
    ["/"] = "_",
  }

  base64url_encode = function(value)
    value = ngx_encode_base64(value, true)
    if not value then
      return nil
    end

    return string_gsub(value, BASE64URL_ENCODE_CHARS, BASE64URL_ENCODE_SUBST)
  end


  local BASE64URL_DECODE_CHARS = "[-_]"
  local BASE64URL_DECODE_SUBST = {
    ["-"] = "+",
    ["_"] = "/",
  }

  base64url_decode = function(value)
    value = string_gsub(value, BASE64URL_DECODE_CHARS, BASE64URL_DECODE_SUBST)
    return ngx_decode_base64(value)
  end
end


-- authenticated_userid'den token, username, password çıkar
-- Backward compatibility: eski tokenlar düz string, yeni tokenlar JSON
local function parse_authenticated_userid(authenticated_userid)
  if not authenticated_userid or authenticated_userid == "" then
    return nil, nil, nil
  end
  
  -- JSON mı kontrol et
  local success, parsed = pcall(cjson.decode, authenticated_userid)
  if success and type(parsed) == "table" and parsed.token then
    -- Yeni format: JSON
    return parsed.token, parsed.username, parsed.password
  else
    -- Eski format: düz token string
    return authenticated_userid, nil, nil
  end
end


-- Token, username, password'ü JSON olarak birleştir
local function build_authenticated_userid(token, username, password)
  if username and password then
    return cjson.encode({
      token = token,
      username = username,
      password = password
    })
  else
    -- Username/password yoksa düz token döndür (backward compat)
    return token
  end
end


local function generate_token(conf, service, credential, authenticated_userid,
                              scope, state, disable_refresh, existing_token)

  local token_expiration = conf.token_expiration

  local refresh_token_ttl
  if conf.refresh_token_ttl and conf.refresh_token_ttl > 0 then
    refresh_token_ttl = conf.refresh_token_ttl
  end

  local service_id
  if not conf.global_credentials then
    service_id = service.id
  end

  local refresh_token
  local token, err
  
  if existing_token then
    -- REFRESH GRANT: Her refresh'te identity servisine git ve authenticated_userid'yi yenile
    
    -- Mevcut token'dan username/password çıkar (backward compat)
    local current_identity_token, stored_username, stored_password = parse_authenticated_userid(existing_token.authenticated_userid)
    
    local new_authenticated_userid = existing_token.authenticated_userid  -- varsayılan: eskisini koru
    
    -- Username/password varsa identity servisine git
    if conf.identity_url and stored_username and stored_password then
      local httpc = http.new()
      
      local identity_body = {
        application = stored_username,
        apiKey = stored_password,
      }
      
      local json_body = cjson.encode(identity_body)
      
      local res, identity_err = httpc:request_uri(conf.identity_url, {
        method = "POST",
        body = json_body,
        headers = {
          ["Content-Type"] = "application/json",
          ["Content-Length"] = #json_body,
        }
      })
      
      if identity_err or not res then
        return kong.response.exit(500, {
          error = "invalid_request",
          error_description = "Identity service request failed"
        })
      end
      
      if res.status ~= 200 then
        return kong.response.exit(401, {
          error = "Kimlik dogrulama ve yetkilendirme hatasi",
          ["error-code"] = "202",
          error_description = "Identity service authentication failed"
        })
      end
      
      -- Identity servisinden yeni token al
      local identity_response = cjson.decode(res.body)
      local new_identity_token = identity_response.token
      
      -- Yeni authenticated_userid oluştur (username/password ile birlikte)
      new_authenticated_userid = build_authenticated_userid(new_identity_token, stored_username, stored_password)
      
      kong.log.info("Identity token refreshed during refresh_token grant")
    end
    
    -- Yeni refresh token üret
    refresh_token = random_string()
    
    -- Sabit 1 saat expiration (KKB spesifikasyonu)
    token_expiration = 3600
    
    -- Eski token'i DB'den sil ve tum worker'lardaki cache'i temizle
    local old_access_token = existing_token.access_token
    local old_token_id = existing_token.id
    
    kong.log.err("[ige-oauth2] REFRESH: START - credential_id=", credential.id, " old_token_id=", old_token_id, " old_access_token=", old_access_token)
    
    -- RAW SQL ile credential'a ait TUM tokenlari sil (Kong DAO bypass)
    local delete_sql = "DELETE FROM oauth2_tokens WHERE credential_id = '" .. credential.id .. "'"
    kong.log.err("[ige-oauth2] REFRESH: executing SQL: ", delete_sql)
    local del_res, del_err = kong.db.connector:query(delete_sql)
    if del_err then
      kong.log.err("[ige-oauth2] REFRESH: RAW SQL DELETE failed: ", del_err)
      -- Fallback: DAO ile dene
      local _, dao_err = kong.db.oauth2_tokens:delete({ id = old_token_id })
      if dao_err then
        kong.log.err("[ige-oauth2] REFRESH: DAO DELETE also failed: ", dao_err)
      end
    else
      kong.log.err("[ige-oauth2] REFRESH: RAW SQL DELETE success, affected rows=", del_res and del_res.affected_rows or "unknown")
    end
    
    -- Cache invalidate (defense in depth)
    if old_access_token then
      local token_cache_key = kong.db.oauth2_tokens:cache_key(old_access_token)
      kong.cache:invalidate(token_cache_key)
    end
    
    -- RAW SQL ile verify: eski token gercekten silindi mi?
    local verify_sql = "SELECT id, access_token FROM oauth2_tokens WHERE access_token = '" .. old_access_token .. "' LIMIT 1"
    local verify_res, verify_err = kong.db.connector:query(verify_sql)
    if verify_err then
      kong.log.err("[ige-oauth2] REFRESH: verify query failed: ", verify_err)
    elseif verify_res and #verify_res > 0 then
      kong.log.err("[ige-oauth2] REFRESH: !!!CRITICAL!!! old token STILL EXISTS after RAW SQL DELETE! id=", verify_res[1].id)
    else
      kong.log.err("[ige-oauth2] REFRESH: VERIFIED - old token deleted successfully from DB")
    end
    
    -- Credential'a ait kalan token var mi kontrol et
    local remaining_sql = "SELECT count(*) as cnt FROM oauth2_tokens WHERE credential_id = '" .. credential.id .. "'"
    local remaining_res = kong.db.connector:query(remaining_sql)
    if remaining_res and remaining_res[1] then
      kong.log.err("[ige-oauth2] REFRESH: remaining tokens for this credential: ", remaining_res[1].cnt)
    end
    
    -- Yeni token oluştur (güncellenmiş authenticated_userid ile)
    token, err = kong.db.oauth2_tokens:insert({
      service = service_id and { id = service_id } or nil,
      credential = { id = credential.id },
      authenticated_userid = new_authenticated_userid,
      expires_in = token_expiration,
      refresh_token = refresh_token,
      scope = scope or existing_token.scope
    }, {
      ttl = token_expiration > 0 and refresh_token_ttl or nil
    })
    
  else
    -- PASSWORD GRANT: Identity servisine git
    local request_body = kong.request.get_body()
    local httpc = http.new()

    -- İstek URL'si ve body verisi
    local url = conf.identity_url--res[1].config_value--"https://stage-ides-service.cloudpeer.com/v1/identity/user-password"
    local body = {
        application = request_body.username,--"AppSvc-0060",   -- Parametrik değerler, değişkenlerden alınabilir
        apiKey = request_body.password,--"Krisp01!",      -- Parametrik değerler, değişkenlerden alınabilir
    }
  
    local json_body = cjson.encode(body)
  
    local res, err = httpc:request_uri(url, {
        method = "POST",
        body = json_body,
        headers = {
            ["Content-Type"] = "application/json",
            ["Content-Length"] = #json_body,
        }
    })
      if err then
    return error(err)
  end
    if not res then
kong.response.exit(500, { message = "The request failed due to some unknown reason", error = "invalid_request" })
    end
  
    if res.status ~= 200  then
       kong.response.exit(401,  {
        error = "Kimlik dogrulama ve yetkilendirme hatasi", 
        ["error-code"] = "202", 
        error_description = "scope, username, password, client_id, client_secret girdilerinizi kontrol ediniz"
      })
  end
    local response_body = res.body
    local response_data, parse_err = cjson.decode(response_body)
    local token_access = response_data.token
    local password_req = request_body.password
    
    -- Identity servisinden refresh_token geldiyse onu kullan, yoksa random üret
    if response_data.refresh_token then
      refresh_token = response_data.refresh_token
    elseif not disable_refresh and token_expiration > 0 then
      refresh_token = random_string()
    end
    
    -- PASSWORD GRANT: Credential'a ait TUM eski tokenlari sil (yeni token eskileri ezer)
    kong.log.err("[ige-oauth2] PASSWORD_GRANT: deleting old tokens for credential_id=", credential.id)
    local delete_sql = "DELETE FROM oauth2_tokens WHERE credential_id = '" .. credential.id .. "'"
    local del_res, del_err = kong.db.connector:query(delete_sql)
    if del_err then
      kong.log.err("[ige-oauth2] PASSWORD_GRANT: RAW SQL DELETE failed: ", del_err)
    else
      kong.log.err("[ige-oauth2] PASSWORD_GRANT: RAW SQL DELETE success, deleted old tokens for credential")
    end
    
    token, err = kong.db.oauth2_tokens:insert({
      service = service_id and { id = service_id } or nil,
      credential = { id = credential.id },
      authenticated_userid = build_authenticated_userid(token_access, request_body.username, request_body.password),
      expires_in = token_expiration,
      refresh_token = refresh_token,
      scope = scope
    }, {
      -- Access tokens (and their associated refresh token) are being
      -- permanently deleted after 'refresh_token_ttl' seconds
      ttl = token_expiration > 0 and refresh_token_ttl or nil
    })
  end

 

  return {
    access_token = token.access_token,
    token_type = "Bearer", -- KKB ile ayni olmasi icin bearer->Bearer
    expires_in = token_expiration > 0 and token.expires_in or nil,
    refresh_token = refresh_token,
    state = nil, --If state is nil, this value won't be added KKB ile ayni olmasi icin state->nil
    scope = scope
  }
end


local function load_oauth2_credential_by_client_id(client_id)
  local credential, err = kong.db.oauth2_credentials:select_by_client_id(client_id)
  if err then
    return nil, err
  end

  return credential
end


local function get_redirect_uris(client_id)
  local client, err
  if type(client_id) == "string" and client_id ~= "" then
    local credential_cache_key = kong.db.oauth2_credentials:cache_key(client_id)
    client, err = kong.cache:get(credential_cache_key, nil,
                                 load_oauth2_credential_by_client_id,
                                 client_id)
    if err then
      return error(err)
    end
  end

  return client and client.redirect_uris or nil, client
end


local function retrieve_parameters()
  -- OAuth2 parameters could be in both the querystring or body
  local uri_args = kong.request.get_query()
  local method   = kong.request.get_method()

  if method == "POST" or method == "PUT" or method == "PATCH" then
    local body_args = kong.request.get_body()

    return kong.table.merge(uri_args, body_args)
  end

  return uri_args
end


local function retrieve_scope(parameters, conf)
  local scope = parameters[SCOPE]
  local scopes = {}

  if conf.scopes and scope ~= nil then
    if type(scope) ~= "string" then
      return nil, {[ERROR] = "invalid_scope", error_description = "scope must be a string"}
    end

    for v in scope:gmatch("%S+") do
      if not table_contains(conf.scopes, v) then  -- scope yerine v kullanıldı
        return nil, {[ERROR] = "invalid_scope", error_description = "\"" .. v .. "\" is an invalid " .. SCOPE}
      else
        table.insert(scopes, v)
      end
    end

  elseif not scope and conf.mandatory_scope then
    return nil, {[ERROR] = "invalid_scope", error_description = "You must specify a " .. SCOPE}
  end

  if scope and not conf.scopes then
    return scope
  end

  if #scopes > 0 then
    return table.concat(scopes, " ")
  end

  return scope
end

local function retrieve_code_challenge(parameters)
  local challenge        = parameters[CODE_CHALLENGE]
  local challenge_method = parameters[CODE_CHALLENGE_METHOD]

  if challenge_method and not challenge then
    return nil, CODE_CHALLENGE .. " is required when code_method is present"
  end

  if challenge then
    local challenge_decoded = base64url_decode(challenge)
    if challenge_decoded then
      challenge = base64url_encode(challenge_decoded)
    end

    if challenge_method and challenge_method ~= "S256" then
      if challenge_method ~= "s256" then
        return nil, CODE_CHALLENGE_METHOD .. " is not supported, must be S256"
      end

      challenge_method = "S256"
    end
  end

  return challenge, nil, challenge_method or "S256"
end

local function requires_pkce(conf, client, used_pkce)
  if not client then
    return false
  end

  if used_pkce -- only set on token endpoint
  or (client.client_type == CLIENT_TYPE_PUBLIC       and conf.pkce ~= "none")
  or (client.client_type == CLIENT_TYPE_CONFIDENTIAL and conf.pkce == "strict")
  then
    return true
  end

  return false
end

local function authorize(conf)
  local response_params = {}
  local parameters = retrieve_parameters()
  local state = parameters[STATE]
  local allowed_redirect_uris, client, redirect_uri, parsed_redirect_uri
  local is_implicit_grant

  local is_https, err = check_https(kong.ip.is_trusted(kong.client.get_ip()),
                                    conf.accept_http_if_already_terminated)
  if not is_https then
    response_params = {
      [ERROR] = "access_denied",
      error_description = err or "You must use HTTPS"
    }

  else
    if conf.provision_key ~= parameters.provision_key then
      response_params = {
        [ERROR] = "invalid_request",
        error_description = "Missing or duplicate parameters"
      }

    elseif not parameters.authenticated_userid or strip(parameters.authenticated_userid) == "" then
      response_params = {
        [ERROR] = "invalid_request",
        error_description = "Missing or duplicate parameters"
      }

    else
      local response_type = parameters[RESPONSE_TYPE]

      -- Check response_type
      if not ((response_type == CODE and conf.enable_authorization_code) or
              (conf.enable_implicit_grant and response_type == TOKEN)) then
        -- Auth Code Grant (http://tools.ietf.org/html/rfc6749#section-4.1.1)
        response_params = {
          [ERROR] = "unsupported_response_type",
          error_description = "Invalid " .. RESPONSE_TYPE
        }
      end
      
      -- Check scopes
      local scopes, err = retrieve_scope(parameters, conf)
      if err then
        response_params = err -- If it's not ok, then this is the error message
      end

      -- Check client_id and redirect_uri
      allowed_redirect_uris, client = get_redirect_uris(parameters[CLIENT_ID])

      if not allowed_redirect_uris then
        response_params = {
          [ERROR] = "invalid_request",
          error_description = "Missing or duplicate parameters"
        }

      else
        redirect_uri = parameters[REDIRECT_URI] and
                       parameters[REDIRECT_URI] or
                       allowed_redirect_uris[1]

        if not table_contains(allowed_redirect_uris, redirect_uri) then
          response_params = {
            [ERROR] = "invalid_request",
            error_description = "Invalid " .. REDIRECT_URI ..
                                " that does not match with any redirect_uri" ..
                                " created with the application"
          }

          -- redirect_uri used in this case is the first one registered with
          -- the application
          redirect_uri = allowed_redirect_uris[1]
        end
      end

      parsed_redirect_uri = url.parse(redirect_uri)

      local challenge, err, challenge_method = retrieve_code_challenge(parameters)
      if err then
        response_params = {
          [ERROR] = "invalid_request",
          error_description = err
        }
      elseif client and not challenge and requires_pkce(conf, client) then
        response_params = {
          [ERROR] = "invalid_request",
          error_description = CODE_CHALLENGE .. " is required for " .. client.client_type .. " clients"
        }
      elseif not challenge then -- do not save a code method unless we have a challenge
        challenge_method = nil
      end

      -- If there are no errors, keep processing the request
      if not response_params[ERROR] then
        if response_type == CODE then
          local service_id
          if not conf.global_credentials then
            service_id = (kong.router.get_service() or EMPTY).id
          end

          local auth_code, err = kong.db.oauth2_authorization_codes:insert({
            service = service_id and { id = service_id } or nil,
            credential = { id = client.id },
            authenticated_userid = parameters[AUTHENTICATED_USERID],
            scope = scopes,
            challenge = challenge,
            challenge_method = challenge_method,
            plugin = { id  = kong.plugin.get_id() },
          }, {
            ttl = 300
          })

          if err then
            error(err)
          end

          response_params = {
            code = auth_code.code,
          }

        else
          -- Implicit grant, override expiration to zero
          response_params = generate_token(conf, kong.router.get_service(),
                                           client,
                                           parameters[AUTHENTICATED_USERID],
                                           scopes, state, true)
          is_implicit_grant = true
        end
      end
    end
  end

  -- Adding the state if it exists. If the state == nil then it won't be added
  response_params.state = nil

  -- Appending kong generated params to redirect_uri query string
  if parsed_redirect_uri then
    local encoded_params = encode_args(kong.table.merge(ngx_decode_args(
      (is_implicit_grant and
        (parsed_redirect_uri.fragment and parsed_redirect_uri.fragment or "") or
        (parsed_redirect_uri.query and parsed_redirect_uri.query or "")
      )), response_params))

    if is_implicit_grant then
      parsed_redirect_uri.fragment = encoded_params
    else
      parsed_redirect_uri.query = encoded_params
    end
  end

  -- Sending response in JSON format
  local status = response_params[ERROR] and 400 or 200
  local body
  if redirect_uri then
    body = { redirect_uri = url.build(parsed_redirect_uri) }

  else
    body = response_params
  end

  return kong.response.exit(status, body, {
    ["cache-control"] = "no-store",
    ["pragma"] = "no-cache"
  })
end


local function retrieve_client_credentials(parameters, conf)
  local client_id, client_secret, from_authorization_header
  local authorization_header = kong.request.get_header(conf.auth_header_name)

  if parameters[CLIENT_ID] and parameters[CLIENT_SECRET] then
    client_id = parameters[CLIENT_ID]
    client_secret = parameters[CLIENT_SECRET]

  elseif authorization_header then
    from_authorization_header = true

    local iterator, iter_err = ngx_re_gmatch(authorization_header,
                                             "\\s*[Bb]asic\\s*(.+)",
                                             "jo")
    if not iterator then
      kong.log.err(iter_err)
      return
    end

    local m, err = iterator()
    if err then
      kong.log.err(err)
      return
    end

    if m and next(m) then
      local decoded_basic = ngx_decode_base64(m[1])
      if decoded_basic then
        local basic_parts = split(decoded_basic, ":")
        client_id = basic_parts[1]
        client_secret = basic_parts[2]
      end
    end

  elseif parameters[CLIENT_ID] then
    client_id = parameters[CLIENT_ID]
  end

  return client_id, client_secret, from_authorization_header
end

local function validate_pkce_verifier(parameters, auth_code)
  local verifier = parameters[CODE_VERIFIER]
  if not verifier then
    return {
      [ERROR] = "invalid_request",
      error_description = CODE_VERIFIER .. " is required for PKCE authorization requests",
    }
  elseif type(verifier) ~= "string" then
    return {
      [ERROR] = "invalid_request",
      error_description = CODE_VERIFIER .. " is not a string",
    }
  end

  if #verifier < 43 or #verifier > 128 then
    return {
      [ERROR] = "invalid_request",
      error_description = CODE_VERIFIER .. " must be between 43 and 128 characters",
    }
  end

  local challenge = sha256_base64url(verifier)

  if not challenge
  or not auth_code.challenge
  or challenge ~= auth_code.challenge
  then
    return {
      [ERROR] = "invalid_grant",
      error_description = "The given grant is invalid"
    }
  end

  return nil
end

local function issue_token(conf)
  local response_params = {}
  local invalid_client_properties = {}

  local parameters = retrieve_parameters()
  local state = parameters[STATE]

  local is_https, err = check_https(kong.ip.is_trusted(kong.client.get_ip()),
                                    conf.accept_http_if_already_terminated)
  if not is_https then
    response_params = {
      [ERROR] = "access_denied",
      error_description = err or "You must use HTTPS"
    }

  else
    local grant_type = parameters[GRANT_TYPE]
    if not grant_type or grant_type == "" then
      response_params = {
         [ERROR] = "invalid_request",
         error_description = "Missing required parameter: grant_type"
      }
    elseif not (grant_type == GRANT_AUTHORIZATION_CODE or
            grant_type == GRANT_REFRESH_TOKEN or
            (conf.enable_client_credentials and
             grant_type == GRANT_CLIENT_CREDENTIALS) or
            (conf.enable_password_grant and grant_type == GRANT_PASSWORD)) then
      response_params = {
         [ERROR] = "unsupported_grant_type",
         error_description = "Unsupported grant type: " .. tostring(grant_type)
      }
    end

    local client_id, client_secret, from_authorization_header =
      retrieve_client_credentials(parameters, conf)

    -- Check client_id and redirect_uri
    local allowed_redirect_uris, client = get_redirect_uris(client_id)
    if grant_type ~= GRANT_CLIENT_CREDENTIALS then
      if allowed_redirect_uris then
        local redirect_uri = parameters[REDIRECT_URI] and
          parameters[REDIRECT_URI] or
          allowed_redirect_uris[1]

        if not table_contains(allowed_redirect_uris, redirect_uri) then
          response_params = {
            [ERROR] = "invalid_request",
            error_description = "Missing or duplicate parameters"
          }
        end

      else
        response_params = {
          [ERROR] = "invalid_request",
          error_description = "Missing or duplicate parameters"
        }

        if from_authorization_header then
          invalid_client_properties = {
            status = 401,
            www_authenticate = "Basic realm=\"OAuth2.0\""
          }
        end
      end
    end

    if client then
      if client.client_type == CLIENT_TYPE_CONFIDENTIAL then
        local authenticated
        if client.hash_secret then
          authenticated = secret.verify(client_secret, client.client_secret)
          if authenticated and secret.needs_rehash(client.client_secret) then
            local pk = kong.db.oauth2_credentials.schema:extract_pk_values(client)
            local ok, err = kong.db.oauth2_credentials:update(pk, {
              client_secret = client_secret,
              hash_secret   = true,
            })

            if not ok then
              kong.log.warn(err)
            end
          end

        else
          authenticated = client.client_secret == client_secret
        end

        if not authenticated then
          response_params = {
            [ERROR] = "invalid_request",
          error_description = "Missing or duplicate parameters"
          }

          if from_authorization_header then
            invalid_client_properties = {
              status = 401,
              www_authenticate = "Basic realm=\"OAuth2.0\""
            }
          end
        end

      elseif client.client_type == CLIENT_TYPE_PUBLIC and strip(client_secret) ~= "" then
        response_params = {
           [ERROR] = "invalid_request",
           error_description = "Missing or duplicate parameters"
        }
      end
    end

    if not response_params[ERROR] then
      if grant_type == GRANT_AUTHORIZATION_CODE then
        local code = parameters[CODE]

        local service_id
        if not conf.global_credentials then
          service_id = (kong.router.get_service() or EMPTY).id
        end

        local auth_code =
          code and kong.db.oauth2_authorization_codes:select_by_code(code)
        if not auth_code or (service_id and service_id ~= auth_code.service.id) then
          response_params = {
             [ERROR] = "invalid_request",
             error_description = "Missing or duplicate parameters"
          }
        elseif auth_code.credential.id ~= client.id then
          response_params = {
            [ERROR] = "invalid_request",
            error_description = "Missing or duplicate parameters"
          }
        end

        -- if the code was generated by a PKCE request, then check the code verifier
        local client_requires_pkce = auth_code and requires_pkce(conf, client, auth_code.challenge_method)
        if not response_params[ERROR] and client_requires_pkce then
          local err = validate_pkce_verifier(parameters, auth_code)
          if err then
            response_params = err
          end
        end

        if not response_params[ERROR] and conf.global_credentials then
          -- verify only if plugin is present to avoid existing codes being fails
          if auth_code.plugin and
             (kong.plugin.get_id() ~= auth_code.plugin.id) then
            response_params = {
              [ERROR] = "invalid_request",
              error_description = "Missing or duplicate parameters"
            }
          end
        end

        if not response_params[ERROR] then
          if not auth_code or (service_id and service_id ~= auth_code.service.id)
          then
            response_params = {
              [ERROR] = "invalid_request",
              error_description = "Missing or duplicate parameters"
            }

          elseif auth_code.credential.id ~= client.id then
            response_params = {
              [ERROR] = "invalid_request",
              error_description = "Missing or duplicate parameters"
            }

          else
            response_params = generate_token(conf, kong.router.get_service(),
              client,
              auth_code.authenticated_userid,
              auth_code.scope, state)

            -- Delete authorization code so it cannot be reused
            kong.db.oauth2_authorization_codes:delete(auth_code)
          end
        end

      elseif grant_type == GRANT_CLIENT_CREDENTIALS then
        -- Only check the provision_key if the authenticated_userid is being set
        if parameters.authenticated_userid and
           conf.provision_key ~= parameters.provision_key then
          response_params = {
             [ERROR] = "invalid_request",
             error_description = "Missing or duplicate parameters"
          }

        elseif not client then
          response_params = {
            [ERROR] = "invalid_request",
            error_description = "Missing or duplicate parameters"
          }

        else
          -- Check scopes
          local scope, err = retrieve_scope(parameters, conf)
          if err then
            -- If it's not ok, then this is the error message
            response_params = err

          else
            response_params = generate_token(conf, kong.router.get_service(),
                                             client,
                                             parameters.authenticated_userid,
                                             scope, state, true)
          end
        end

      elseif grant_type == GRANT_PASSWORD then
        -- Check that it comes from the right client
--        if conf.provision_key ~= parameters.password then
 --         response_params = {
   --          [ERROR] = "invalid_request",
     --        error_description = "Missing or duplicate parameters"
       --   }
        
        if not parameters.username or 
               strip(parameters.username) == "" then
          response_params = {
             [ERROR] = "invalid_request",
              error_description = "Missing or duplicate parameters"
          }
        

        else
          -- Check scopes
          local scope, err  = retrieve_scope(parameters, conf)
          if err then
            -- If it's not ok, then this is the error message
            response_params = err

          else
            response_params = generate_token(conf, kong.router.get_service(),
                                             client,
                                             parameters.authenticated_userid,
                                             scope, state)
          end
        end

      elseif grant_type == GRANT_REFRESH_TOKEN then
        local refresh_token = parameters[REFRESH_TOKEN]

        if not refresh_token or refresh_token == "" then
          response_params = {
             [ERROR] = "invalid_request",
              error_description = "Missing required parameter: refresh_token"
          }
        else
          local service_id
          if not conf.global_credentials then
            service_id = (kong.router.get_service() or EMPTY).id
          end

          local token = kong.db.oauth2_tokens:select_by_refresh_token(refresh_token)

          if not token or (service_id and service_id ~= token.service.id) then
            response_params = {
               [ERROR] = "invalid_grant",
                error_description = "Refresh token is invalid, expired, or has been revoked"
            }

          -- Check that the token belongs to the client application
          elseif token.credential.id ~= client.id then
              response_params = {
                [ERROR] = "invalid_grant",
                error_description = "Refresh token was issued to another client"
              }

          else
           
              response_params = generate_token(conf, kong.router.get_service(),
                                               client,
                                               token.authenticated_userid,
                                               token.scope, state, false, token)
              -- Eski token generate_token içinde siliniyor (KKB'de zaten geçersiz)
          end
        end
      end
    end
  end

  -- Adding the state if it exists. If the state == nil then it won't be added
  response_params.state = nil

  -- Sending response in JSON format
  local error_status = 400
  if response_params[ERROR] then
    if invalid_client_properties and invalid_client_properties.status then
      error_status = invalid_client_properties.status
    elseif response_params[ERROR] == "invalid_grant" then
      error_status = 401
    end
  end

  return kong.response.exit(response_params[ERROR] and error_status or 200,
                             response_params, {
                               ["cache-control"] = "no-store",
                               ["pragma"] = "no-cache",
                               ["www-authenticate"] = invalid_client_properties and
                                                      invalid_client_properties.www_authenticate
                             }
                           )
end


local function load_token(access_token)
  return kong.db.oauth2_tokens:select_by_access_token(access_token)
end


local function retrieve_token(conf, access_token, realm)
  -- Token dogrulamada her zaman DB'den oku.
  -- Revoke edilen tokenlar aninda gecersiz olur, cache stale riski sifir.
  kong.log.err("[ige-oauth2] RETRIEVE_TOKEN: checking access_token=", access_token)
  
  -- RAW SQL ile dogrudan PostgreSQL'den kontrol et (tum Kong katmanlarini bypass)
  local sql = "SELECT id, access_token, credential_id, service_id, authenticated_userid, scope, expires_in, created_at, token_type, refresh_token FROM oauth2_tokens WHERE access_token = '" .. access_token .. "' LIMIT 1"
  local sql_res, sql_err = kong.db.connector:query(sql)
  
  if sql_err then
    kong.log.err("[ige-oauth2] RETRIEVE_TOKEN: RAW SQL error: ", sql_err, " - falling back to DAO")
    -- Fallback to DAO
    local token, err = load_token(access_token)
    if err then return error(err) end
    if not token then
      kong.log.err("[ige-oauth2] RETRIEVE_TOKEN: DAO also returned nil")
      return
    end
    kong.log.err("[ige-oauth2] RETRIEVE_TOKEN: DAO returned token id=", token.id)
    
    if not conf.global_credentials then
      if not token.service then
        return kong.response.exit(401, {
          error = "Kimlik dogrulama ve yetkilendirme hatasi", 
          ["error-code"] = "202", 
          error_description = "scope, username, password, client_id, client_secret girdilerinizi kontrol ediniz"
        },
        {
          ["WWW-Authenticate"] = 'Bearer' .. realm .. ' error=' ..
                                  '"invalid_token" error_description=' ..
                                  '"The access token is invalid or has expired"'
        })
      end
    end
    return token
  end
  
  if not sql_res or #sql_res == 0 then
    kong.log.err("[ige-oauth2] RETRIEVE_TOKEN: RAW SQL - token NOT FOUND in DB (returning 401)")
    return
  end
  
  kong.log.err("[ige-oauth2] RETRIEVE_TOKEN: RAW SQL - token FOUND id=", sql_res[1].id, " credential_id=", sql_res[1].credential_id)
  
  -- DAO ile de al (Kong'un beklediği format için)
  local token, err = load_token(access_token)
  if err then return error(err) end
  if not token then
    kong.log.err("[ige-oauth2] RETRIEVE_TOKEN: MISMATCH! RAW SQL found token but DAO returned nil!")
    return
  end

  if not conf.global_credentials then
    if not token.service then
      return kong.response.exit(401, {
        error = "Kimlik dogrulama ve yetkilendirme hatasi", 
        ["error-code"] = "202", 
        error_description = "scope, username, password, client_id, client_secret girdilerinizi kontrol ediniz"
      },
      {
        ["WWW-Authenticate"] = 'Bearer' .. realm .. ' error=' ..
                                '"invalid_token" error_description=' ..
                                '"The access token is invalid or has expired"'
      })
    end
   -- token aldigimiz gateway servis ile istek yaptigimiz gateway servis farkli oldugu icin commentledik
   -- if token.service.id ~= kong.router.get_service().id then
   --    return nil
   -- end
  end

  return token
end


local function parse_access_token(conf)
  local found_in = {}

  local access_token = kong.request.get_header(conf.auth_header_name)
 
  if access_token then
    local parts = {}
    for v in access_token:gmatch("%S+") do -- Split by space
      table.insert(parts, v)
    end

    if #parts == 2 and (parts[1]:lower() == "token" or
                        parts[1]:lower() == "bearer") then
      access_token = parts[2]
      found_in.authorization_header = true
    end

  else
    access_token = retrieve_parameters()[ACCESS_TOKEN]
    if type(access_token) ~= "string" then
      return
    end
  end

  if conf.hide_credentials then
    if found_in.authorization_header then
      kong.service.request.clear_header(conf.auth_header_name)

    else
      -- Remove from querystring
      local parameters = kong.request.get_query()
      parameters[ACCESS_TOKEN] = nil
      kong.service.request.set_query(parameters)

      local content_type = kong.request.get_header("content-type")
      local is_form_post = content_type and
        string_find(content_type, "application/x-www-form-urlencoded", 1, true)

      if kong.request.get_method() ~= "GET" and is_form_post then
        -- Remove from body
        parameters = kong.request.get_body() or {}
        parameters[ACCESS_TOKEN] = nil
        kong.service.request.set_body(parameters)
      end
    end
  end

  return access_token
end


local function load_oauth2_credential_into_memory(credential_id)
  local result, err = kong.db.oauth2_credentials:select({ id = credential_id })
  if err then
    return nil, err
  end

  return result
end


local function set_consumer(consumer, credential, token, identity_token)
  kong.client.authenticate(consumer, credential)

  local set_header = kong.service.request.set_header
  local clear_header = kong.service.request.clear_header


  if consumer and consumer.id then
    set_header(constants.HEADERS.CONSUMER_ID, consumer.id)
  else
    clear_header(constants.HEADERS.CONSUMER_ID)
  end

  if consumer and consumer.custom_id then
    set_header(constants.HEADERS.CONSUMER_CUSTOM_ID, consumer.custom_id)
  else
    clear_header(constants.HEADERS.CONSUMER_CUSTOM_ID)
  end

  if consumer and consumer.username then
    set_header(constants.HEADERS.CONSUMER_USERNAME, consumer.username)
  else
    clear_header(constants.HEADERS.CONSUMER_USERNAME)
  end

  if credential and credential.client_id then
    set_header(constants.HEADERS.CREDENTIAL_IDENTIFIER, credential.client_id)
  else
    clear_header(constants.HEADERS.CREDENTIAL_IDENTIFIER)
  end

  if credential then
    clear_header(constants.HEADERS.ANONYMOUS)
  else
    set_header(constants.HEADERS.ANONYMOUS, true)
  end

  if token and token.scope then
    set_header("X-Authenticated-Scope", token.scope)
local headers = ngx.req.get_headers()
  local authorization_header = headers["Authorization"]
  local coming_token  = authorization_header:match("Bearer%s+(.+)")
if not coming_token then
  return  kong.response.exit(400, {
          [ERROR] = "invalid_request",
          error_description = "Missing or duplicate parameters"
        })
end
  
     
  else
    clear_header("X-Authenticated-Scope")
  end

  -- identity_token parametresi varsa onu kullan, yoksa authenticated_userid'den parse et
  local auth_token = identity_token
  if not auth_token and token and token.authenticated_userid then
    auth_token = parse_authenticated_userid(token.authenticated_userid)
  end
  
  if auth_token then
    set_header("X-Authenticated-UserId", auth_token)
    set_header("Authorization", "Bearer " .. auth_token)
  else
    clear_header("X-Authenticated-UserId")
  end
end


local function do_authentication(conf)
  local access_token = parse_access_token(conf);
  local realm = conf.realm and fmt(' realm="%s"', conf.realm) or ''
  if not access_token or access_token == "" then
    return nil, {
      status = 401,
      message = {
        error = "Kimlik dogrulama ve yetkilendirme hatasi",
        ["error-code"] = "202",
        error_description = "scope, username, password, client_id, client_secret girdilerinizi kontrol ediniz"
      },
      headers = {
        ["WWW-Authenticate"] = 'Bearer' .. realm
      }
    }
  end

  local token = retrieve_token(conf, access_token, realm)
  if not token then
    return nil, {
      status = 401,
      message = {
        error = "invalid_token",
        ["error-code"] = "202",
        error_description = "The access token is invalid, expired, or has been revoked"
      },
      headers = {
        ["WWW-Authenticate"] = 'Bearer' .. realm .. ' error=' ..
                               '"invalid_token" error_description=' ..
                               '"The access token is invalid or has expired"'
      }
    }
  end

   -- token aldigimiz gateway servis ile istek yaptigimizi gateway servis farkli oldugu icin commentledik
  if (--token.service and token.service.id and
      --kong.router.get_service().id ~= token.service.id) or(
      (not token.service or not token.service.id) and
        not conf.global_credentials) then
    return nil, {
      status = 401,
      message = {
        error = "invalid_token",
        ["error-code"] = "202",
        error_description = "The access token is not valid for this service"
      },
      headers = {
        ["WWW-Authenticate"] = 'Bearer' .. realm .. ' error=' ..
                               '"invalid_token" error_description=' ..
                               '"The access token is invalid or has expired"'
      }

    }
  end

  -- Check expiration date
  if token.expires_in > 0 then -- zero means the token never expires
    local now = timestamp.get_utc() / 1000
    if now - token.created_at > token.expires_in then
      return nil, {
        status = 401,
        message = {
          error = "invalid_token",
          ["error-code"] = "202",
          error_description = "The access token has expired"
        },
        headers = {
          ["WWW-Authenticate"] = 'Bearer' .. realm .. ' error=' ..
                                 '"invalid_token" error_description=' ..
                                 '"The access token is invalid or has expired"'
        }
      }
    end
  end

  -- Retrieve the credential from the token
  local credential_cache_key =
    kong.db.oauth2_credentials:cache_key(token.credential.id)

  local credential, err = kong.cache:get(credential_cache_key, nil,
                                         load_oauth2_credential_into_memory,
                                         token.credential.id)
  if err then
    return error(err)
  end

  -- authenticated_userid'den identity token'ı çıkar (backward compat - JSON veya düz string)
  local identity_token = parse_authenticated_userid(token.authenticated_userid)

  -- Retrieve the consumer from the credential
  local consumer_cache_key, consumer
  consumer_cache_key = kong.db.consumers:cache_key(credential.consumer.id)
  consumer, err      = kong.cache:get(consumer_cache_key, nil,
                                      kong.client.load_consumer,
                                      credential.consumer.id)
  if err then
    return error(err)
  end

  set_consumer(consumer, credential, token, identity_token)

  return true
end

local function invalid_oauth2_method(endpoint_name, realm)
  return kong.response.exit(405, 
  {
    error = "invalid_method",
    error_description = kong.request.get_method() .. " not permitted"
  },
  {
    ["WWW-Authenticate"] = 'Bearer' .. realm .. ' error="invalid_method" error_description="' ..
                            kong.request.get_method() .. ' not permitted"'
  }
)
end

local function set_anonymous_consumer(anonymous)
  local consumer_cache_key = kong.db.consumers:cache_key(anonymous)
  local consumer, err = kong.cache:get(consumer_cache_key, nil,
                                        kong.client.load_consumer,
                                        anonymous, true)
  if err then
    return error(err)
  end

  if not consumer then
    ---local err_msg = "anonymous consumer " .. anonymous .. " is configured but doesn't exist"
    ---kong.log.err(err_msg)

    --return kong.response.error(500, err_msg)
    local response_body = {
      error = "invalid_request",
      error_description = "The request failed due to some unknown reason"
    }
    return kong.response.exit(500, response_body)
  end

  set_consumer(consumer)
end

--- When conf.anonymous is enabled we are in "logical OR" authentication flow.
--- Meaning - either anonymous consumer is enabled or there are multiple auth plugins
--- and we need to passthrough on failed authentication.
local function logical_OR_authentication(conf)
  if kong.client.get_credential() then
    -- we're already authenticated and in "logical OR" between auth methods -- early exit
    local clear_header = kong.service.request.clear_header
    clear_header("X-Authenticated-Scope")
    clear_header("X-Authenticated-UserId")
    return
  end

  local ok, _ = do_authentication(conf)
  if not ok then
    set_anonymous_consumer(conf.anonymous)
  end
end

--- When conf.anonymous is not set we are in "logical AND" authentication flow.
--- Meaning - if this authentication fails the request should not be authorized
--- even though other auth plugins might have successfully authorized user.
local function logical_AND_authentication(conf)
  local ok, err = do_authentication(conf)
  if not ok then
    return kong.response.exit(err.status, err.message, err.headers)
  end
end

function _M.execute(conf)
  local path = kong.request.get_path()
  local has_end_slash = string_byte(path, -1) == SLASH

  local realm = conf.realm and fmt(' realm="%s"', conf.realm) or ''
  if string_find(path, "/auth/oauth/v2/token", has_end_slash and -22 or -21, true) then
    if kong.request.get_method() ~= "POST" then
      local err = invalid_oauth2_method("authorization", realm)
      return kong.response.exit(err.status, err.message, err.headers)
    
    end
    return issue_token(conf)
  end

  if string_find(path, "/oauth2/authorize", has_end_slash and -18 or -17, true) then
    if kong.request.get_method() ~= "POST" then
      local err = invalid_oauth2_method("authorization", realm)
      return kong.response.exit(err.status, err.message, err.headers)
    end

    return authorize(conf)
  end

  if conf.anonymous then
    return logical_OR_authentication(conf)
  else
    return logical_AND_authentication(conf)
  end
end


return _M















