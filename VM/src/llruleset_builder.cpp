#define llruleset_builder_c

#include <vector>
#include <unordered_map>
#include <algorithm>
#include <cstring>
#include <string_view>

#include "lua.h"
#include "lcommon.h"
#include "lualib.h"
#include "llsl.h"
#include "llruleset_builder.h"

#include "lapi.h"
#include "lgc.h"
#include "lobject.h"
#include "ltable.h"
#include "lstring.h"
#include "lstrbuf.h"
#include "lvm.h"

// Most rulesets back their flags with a single integer field
static constexpr size_t kMaxFlagFields = 4;
// Bounds the per-call value array kept on the stack while serializing
static constexpr size_t kMaxDescs = 64;

struct RulesetBuilderDef
{
    std::vector<RulesetParamDescriptor> descs;     // sorted by tag; .name points into string literals
    std::vector<RulesetFlagDescriptor>  flag_descs;
    std::vector<int>                    flag_fields; // distinct field_tags in flag_descs
    // property name -> index into descs, or ~index into flag_descs
    std::unordered_map<std::string_view, int> name_index;
};

namespace
{
    // Converts the value at TOS to its string representation.
    // Strings, numbers, booleans, vectors, quaternions and UUIDs are converted
    // as by tostring(); everything else is skipped. Never runs script code, since
    // the only metatables involved are our own read-only ones.
    // On success: replaces TOS with a Lua string and returns true.
    // On failure: pops TOS and returns false.
    bool slua_ruleset_to_string(lua_State* L)
    {
        bool convertible = false;
        switch (lua_type(L, -1))
        {
        case LUA_TSTRING:
        case LUA_TNUMBER:
        case LUA_TBOOLEAN:
        case LUA_TVECTOR:
            convertible = true;
            break;
        case LUA_TUSERDATA:
        {
            int tag = lua_userdatatag(L, -1);
            convertible = tag == UTAG_UUID || tag == UTAG_QUATERNION;
            break;
        }
        }

        if (!convertible)
        {
            lua_pop(L, 1);
            return false;
        }

        luaL_tolstring(L, -1, nullptr);
        lua_remove(L, -2);
        return true;
    }

    // Encodes a lua array as a CSV string; emit one tag/value pair.
    // returns the new index into the list table.
    int slua_ruleset_serialize_string_csv(lua_State* L, int list, int idx,
        const RulesetParamDescriptor& desc)
    {
        LuaTable* t = hvalue(luaA_toobject(L, -1));
        int n = luaH_getn(t);
        if (n > 0)
        {
            // Rooted on the stack, and its growth is charged against the script's memory limit
            lua_YieldSafeStrBuf* buf = luaYB_push(L);
            int buf_idx = lua_gettop(L);
            for (int j = 1; j <= n; ++j)
            {
                const TValue* elem = luaH_getnum(t, j);
                if (ttisnil(elem))
                    continue;
                luaA_pushvalue(L, elem);
                if (slua_ruleset_to_string(L))
                {
                    size_t len = 0;
                    const char* s = lua_tolstring(L, -1, &len);
                    size_t escapes = 0;
                    for (size_t k = 0; k < len; ++k)
                    {
                        if (s[k] == '\\' || s[k] == ',')
                            ++escapes;
                    }

                    size_t sep = luaYB_len(buf) != 0 ? 1 : 0;
                    luaYB_ensure(L, buf, sep + len + escapes);
                    if (sep)
                        luaYB_appendchar_unsafe(buf, ',');
                    for (size_t k = 0; k < len; ++k)
                    {
                        if (s[k] == '\\' || s[k] == ',')
                            luaYB_appendchar_unsafe(buf, '\\');
                        luaYB_appendchar_unsafe(buf, s[k]);
                    }
                    lua_pop(L, 1);
                }
            }

            if (luaYB_len(buf) != 0)
            {
                luaYB_tostring(L, buf_idx, true);
                lua_pushinteger(L, desc.tag);
                lua_rawseti(L, list, ++idx);
                lua_rawseti(L, list, ++idx);
            }
            else
            {
                lua_pop(L, 1); // pop the empty buffer
            }
        }
        lua_pop(L, 1); // pop the array

        return idx;
    }


    // Convert a lua table into a series of tag/key/value triples, one per entry,
    // sorted by key.
    // returns the new index into the list table.
    int slua_ruleset_serialize_string_map(lua_State* L, int list, int idx,
        const RulesetParamDescriptor& desc)
    {
        // Collect keys for deterministic ordering. Holding raw pointers is fine:
        // the map is on the stack and nothing below can run script code to mutate it.
        std::vector<TString*> keys;
        for (int index = 0; (index = lua_rawiter(L, -1, index)) >= 0;)
        {
            if (lua_type(L, -2) == LUA_TSTRING)
                keys.push_back(tsvalue(luaA_toobject(L, -2)));
            lua_pop(L, 2);
        }
        std::sort(keys.begin(), keys.end(), [](TString* a, TString* b) {
            return luaV_strcmp(a, b) < 0;
        });

        LuaTable* t = hvalue(luaA_toobject(L, -1));
        for (TString* key : keys)
        {
            const TValue* val = luaH_getstr(t, key);
            if (ttisnil(val))
                continue;
            luaA_pushvalue(L, val);
            if (!slua_ruleset_to_string(L))
                continue;
            lua_pushinteger(L, desc.tag);
            lua_rawseti(L, list, ++idx);
            TValue key_tv;
            setsvalue(L, &key_tv, key);
            luaA_pushvalue(L, &key_tv);
            lua_rawseti(L, list, ++idx);
            lua_rawseti(L, list, ++idx); // value
        }
        lua_pop(L, 1); // pop the table
        return idx;
    }

    // Convert a lua array into a series of tag/value pairs, one per element,
    // preserving order.
    // returns the new index into the list table.
    int slua_ruleset_serialize_string_multi(lua_State* L, int list, int idx,
        const RulesetParamDescriptor& desc)
    {
        LuaTable* t = hvalue(luaA_toobject(L, -1));
        int n = luaH_getn(t);
        for (int j = 1; j <= n; ++j)
        {
            const TValue* elem = luaH_getnum(t, j);
            if (ttisnil(elem))
                continue;
            luaA_pushvalue(L, elem);
            if (slua_ruleset_to_string(L))
            {
                lua_pushinteger(L, desc.tag);
                lua_rawseti(L, list, ++idx);
                lua_rawseti(L, list, ++idx);
            }
        }
        lua_pop(L, 1); // pop the array
        return idx;
    }
}

RulesetBuilderDef* ruleset_builder_def_build(
    const RulesetParamDescriptor* descs,
    size_t                        count
)
{
    auto* def = new RulesetBuilderDef;

    // Copy descriptors. .name pointers reference string literals with static
    // storage duration -- no deep copy needed.
    def->descs.assign(descs, descs + count);

    // Sort by tag for deterministic serialization order.
    std::sort(def->descs.begin(), def->descs.end(),
        [](const RulesetParamDescriptor& a, const RulesetParamDescriptor& b) {
            return a.tag < b.tag;
        });
    LUAU_ASSERT(def->descs.size() <= kMaxDescs);

    for (size_t i = 0; i < def->descs.size(); ++i)
        def->name_index.emplace(def->descs[i].name, int(i));

    return def;
}

void ruleset_builder_def_add_flags(
    RulesetBuilderDef*           def,
    const RulesetFlagDescriptor* descs,
    size_t                       count
)
{
    // .name pointers reference string literals -- no deep copy needed.
    def->flag_descs.assign(descs, descs + count);

    for (const auto& fdesc : def->flag_descs)
    {
        if (std::find(def->flag_fields.begin(), def->flag_fields.end(), fdesc.field_tag) == def->flag_fields.end())
            def->flag_fields.push_back(fdesc.field_tag);
    }
    LUAU_ASSERT(def->flag_fields.size() <= kMaxFlagFields);

    for (size_t i = 0; i < def->flag_descs.size(); ++i)
        def->name_index.emplace(def->flag_descs[i].name, ~int(i));
}

void slua_ruleset_fix_names(lua_State* L, const RulesetBuilderDef* def)
{
    for (const auto& desc : def->descs)
        luaS_fix(luaS_new(L, desc.name));
    for (const auto& fdesc : def->flag_descs)
        luaS_fix(luaS_new(L, fdesc.name));
}

void slua_ruleset_serialize(lua_State* L, int params_idx, const RulesetBuilderDef* def)
{
    // Resolve before pushing the list, which would shift relative indices
    params_idx = lua_absindex(L, params_idx);
    bool has_params = !lua_isnoneornil(L, params_idx);
    if (has_params)
        luaL_checktype(L, params_idx, LUA_TTABLE);

    // list, field value, strbuf, element, tostring call
    luaL_checkstack(L, 8, "ruleset");

    if (!has_params)
    {
        lua_newtable(L);
        return; // empty list
    }

    // Phase 1: walk the keys present, collecting param values by descriptor index
    // and accumulating flag bits per backing field, indexed like def->flag_fields.
    LuaTable* params_h = hvalue(luaA_toobject(L, params_idx));
    const TValue* values[kMaxDescs];
    std::fill(values, values + def->descs.size(), luaO_nilobject);
    int  flag_set_bits[kMaxFlagFields]   = {}; // bits to OR in
    int  flag_clear_bits[kMaxFlagFields] = {}; // bits to AND out
    bool flag_touched[kMaxFlagFields]    = {};
    int  present = 0;
    for (int index = 0; (index = lua_rawiter(L, params_idx, index)) >= 0;)
    {
        if (lua_type(L, -2) != LUA_TSTRING)
        {
            lua_pop(L, 2);
            continue;
        }

        // Holding the pointer is fine: the params table is on the stack and
        // nothing below runs script code to mutate it.
        TString* key = tsvalue(luaA_toobject(L, -2));
        lua_pop(L, 2);

        auto found = def->name_index.find(std::string_view(getstr(key), key->len));
        if (found == def->name_index.end())
            continue;

        const TValue* val = luaH_getstr(params_h, key);
        ++present;
        if (found->second >= 0)
        {
            values[found->second] = val;
            continue;
        }

        const auto& fdesc = def->flag_descs[~found->second];
        bool set;
        if (ttisboolean(val))
            set = bvalue(val) != 0;
        else if (ttisnumber(val))
            set = nvalue(val) != 0.0;
        else
            luaL_error(L, "%s must be a boolean or number", fdesc.name);
        size_t field = std::find(def->flag_fields.begin(), def->flag_fields.end(), fdesc.field_tag) - def->flag_fields.begin();
        flag_touched[field] = true;
        if (set)
            flag_set_bits[field]   |= fdesc.mask;
        else
            flag_clear_bits[field] |= fdesc.mask;
    }

    // Room for a tag/value pair per present key, collections grow it as needed
    lua_createtable(L, 2 * present, 0);
    int list = lua_gettop(L);
    int idx = 0;

    // Phase 2: emit tag/value pairs in tag order.
    for (size_t i = 0; i < def->descs.size(); ++i)
    {
        const auto& desc = def->descs[i];
        int  raw_int = 0;
        bool has_raw = false;

        const TValue* val = values[i];
        has_raw = !ttisnil(val);
        if (has_raw && ttisnumber(val))
            raw_int = lsl_float_to_int(nvalue(val));

        // Integer fields that back flags: merge accumulated bits.
        size_t field = std::find(def->flag_fields.begin(), def->flag_fields.end(), desc.tag) - def->flag_fields.begin();
        if (desc.semantic == 'i' && field < def->flag_fields.size() && flag_touched[field])
        {
            int merged = (raw_int | flag_set_bits[field]) & ~flag_clear_bits[field];
            lua_pushinteger(L, desc.tag);
            lua_rawseti(L, list, ++idx);
            lua_pushinteger(L, merged);
            lua_rawseti(L, list, ++idx);
            continue;
        }

        // 'C': string-csv -- value is a Lua array of strings.
        // Encode as comma-joined string; emit one tag/value pair.
        if (desc.semantic == 'C')
        {
            if (!has_raw || !ttistable(val))
                continue;
            luaA_pushvalue(L, val);
            idx = slua_ruleset_serialize_string_csv(L, list, idx, desc);
            continue;
        }

        // 'M': string-map -- value is a Lua string-keyed table.
        // Emit one tag/key/value triple per entry, in sorted key order.
        if (desc.semantic == 'M')
        {
            if (!has_raw || !ttistable(val))
                continue;
            luaA_pushvalue(L, val);
            idx = slua_ruleset_serialize_string_map(L, list, idx, desc);
            continue;
        }

        // 'N': string-multi -- value is a Lua array of strings.
        // Emit one tag/value pair per element, preserving order.
        if (desc.semantic == 'N')
        {
            if (!has_raw || !ttistable(val))
                continue;
            luaA_pushvalue(L, val);
            idx = slua_ruleset_serialize_string_multi(L, list, idx, desc);
            continue;
        }

        if (!has_raw)
            continue;

        // Append tag then value.
        lua_pushinteger(L, desc.tag);
        lua_rawseti(L, list, ++idx);

        if (desc.semantic == 'b' && ttisboolean(val))
            lua_pushinteger(L, bvalue(val));
        else if (desc.semantic == 'i' && ttisnumber(val))
            lua_pushinteger(L, raw_int);
        else
            luaA_pushvalue(L, val);
        lua_rawseti(L, list, ++idx);
    }
}

bool slua_ruleset_coerce(lua_State* L, int params_idx, const RulesetBuilderDef* def)
{
    // Convert relative index to absolute
    if (params_idx < 0 && params_idx > LUA_REGISTRYINDEX)
        params_idx = lua_gettop(L) + params_idx + 1;

    // Not a table? Leave unchanged.
    if (!lua_istable(L, params_idx))
        return false;

    // Check if this is a dict (no integer key 1) vs sequential list (has key 1).
    LuaTable* h = hvalue(luaA_toobject(L, params_idx));
    bool has_first = !ttisnil(luaH_getnum(h, 1));

    if (has_first)
        return false;  // Sequential list, leave unchanged

    // Check if table has any keys at all.
    bool has_keys = (lua_rawiter(L, params_idx, 0) >= 0);
    if (!has_keys)
        return false;  // Empty table, already a valid empty list
    lua_pop(L, 2);  // Pop key and value pushed by lua_rawiter

    // Serialize dict to flat list (pushes new table on stack)
    slua_ruleset_serialize(L, params_idx, def);

    // Replace original table with serialized list
    lua_replace(L, params_idx);

    return true;
}
