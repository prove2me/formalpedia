-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans023
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans023
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:10.621146+00:00
-- url     : https://prove2.me/theorems/aa0ae3e3-81df-4875-8bc2-a2fdff9883bc
-- title:
--   Endpoint22 Reach Plans023 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans023 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2278`, `ThreeBoundEndpoint22Reachable.plan2279`, `ThreeBoundEndpoint22Reachable.plan2280`, `ThreeBoundEndpoint22Reachable.plan2281`, `ThreeBoundEndpoint22Reachable.plan2282`, `ThreeBoundEndpoint22Reachable.plan2283`, `ThreeBoundEndpoint22Reachable.plan2284`, `ThreeBoundEndpoint22Reachable.plan2214`, `ThreeBoundEndpoint22Reachable.plan2285`, `ThreeBoundEndpoint22Reachable.plan2286`, `ThreeBoundEndpoint22Reachable.plan2287`, `ThreeBoundEndpoint22Reachable.plan2288`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans023.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
def plan2209 : Plan := .step choices96 bits657 plan1057

def plan2210 : Plan := .step choices96 bits658 plan1058

def plan2211 : Plan := .step choices96 bits659 plan1059

def plan2212 : Plan := .step choices96 bits659 plan1060

def plan2213 : Plan := .step choices96 bits669 plan1061

def plan2214 : Plan := .step choices96 bits669 plan1062

def plan2215 : Plan := .step choices96 bits669 plan1063

def plan2216 : Plan := .step choices96 bits669 plan1064

def plan2217 : Plan := .step choices96 bits669 plan1065

def plan2218 : Plan := .step choices96 bits669 plan1066

def plan2219 : Plan := .step choices96 bits655 plan1067

def plan2220 : Plan := .step choices96 bits656 plan1068

def plan2221 : Plan := .step choices96 bits656 plan1069

def plan2222 : Plan := .step choices96 bits655 plan1070

def plan2223 : Plan := .step choices96 bits656 plan1071

def plan2224 : Plan := .step choices96 bits666 plan1072

def plan2225 : Plan := .step choices96 bits666 plan1073

def plan2226 : Plan := .step choices96 bits666 plan1074

def plan2227 : Plan := .step choices96 bits664 plan1075

def plan2228 : Plan := .step choices96 bits665 plan1079

def plan2229 : Plan := .step choices96 bits664 plan1089

def plan2230 : Plan := .step choices96 bits665 plan1093

def plan2231 : Plan := .step choices96 bits668 plan1100

def plan2232 : Plan := .step choices96 bits668 plan1101

def plan2233 : Plan := .step choices96 bits668 plan1102

def plan2234 : Plan := .step choices96 bits667 plan1103

def plan2235 : Plan := .step choices96 bits667 plan1113

def plan2236 : Plan := .step choices96 bits655 plan1127

def plan2237 : Plan := .step choices96 bits656 plan1128

def plan2238 : Plan := .step choices96 bits656 plan1129

def plan2239 : Plan := .step choices96 bits655 plan1130

def plan2240 : Plan := .step choices96 bits656 plan1131

def plan2241 : Plan := .step choices96 bits666 plan1132

def plan2242 : Plan := .step choices96 bits666 plan1133

def plan2243 : Plan := .step choices96 bits666 plan1134

def plan2244 : Plan := .step choices96 bits665 plan1135

def plan2245 : Plan := .step choices96 bits664 plan1145

def plan2246 : Plan := .step choices96 bits665 plan1149

def plan2247 : Plan := .step choices96 bits668 plan1156

def plan2248 : Plan := .step choices96 bits668 plan1157

def plan2249 : Plan := .step choices96 bits668 plan1158

def plan2250 : Plan := .step choices96 bits667 plan1163

def plan2251 : Plan := .step choices97 bits672 plan1061

def plan2252 : Plan := .step choices97 bits672 plan1062

def plan2253 : Plan := .step choices97 bits672 plan1063

def plan2254 : Plan := .step choices97 bits672 plan1064

def plan2255 : Plan := .step choices97 bits672 plan1065

def plan2256 : Plan := .step choices97 bits672 plan1066

def plan2257 : Plan := .step choices97 bits671 plan1100

def plan2258 : Plan := .step choices97 bits671 plan1101

def plan2259 : Plan := .step choices97 bits671 plan1102

def plan2260 : Plan := .step choices97 bits670 plan1103

def plan2261 : Plan := .step choices97 bits670 plan1113

def plan2262 : Plan := .step choices97 bits671 plan1156

def plan2263 : Plan := .step choices97 bits671 plan1157

def plan2264 : Plan := .step choices97 bits671 plan1158

def plan2265 : Plan := .step choices97 bits670 plan1163

def plan2266 : Plan := .step choices100 bits657 plan1046

def plan2267 : Plan := .step choices100 bits658 plan1047

def plan2268 : Plan := .step choices100 bits658 plan1048

def plan2269 : Plan := .step choices100 bits657 plan1049

def plan2270 : Plan := .step choices100 bits658 plan1050

def plan2271 : Plan := .step choices100 bits659 plan1051

def plan2272 : Plan := .step choices100 bits659 plan1052

def plan2273 : Plan := .step choices100 bits659 plan1053

def plan2274 : Plan := .step choices100 bits659 plan1054

def plan2275 : Plan := .step choices100 bits658 plan1055

def plan2276 : Plan := .step choices100 bits658 plan1056

def plan2277 : Plan := .step choices100 bits657 plan1057

def plan2278 : Plan := .step choices100 bits658 plan1058

def plan2279 : Plan := .step choices100 bits659 plan1059

def plan2280 : Plan := .step choices100 bits659 plan1060

def plan2281 : Plan := .step choices100 bits669 plan1061

def plan2282 : Plan := .step choices100 bits669 plan1062

def plan2283 : Plan := .step choices100 bits669 plan1063

def plan2284 : Plan := .step choices100 bits669 plan1064

def plan2285 : Plan := .step choices100 bits669 plan1065

def plan2286 : Plan := .step choices100 bits669 plan1066

def plan2287 : Plan := .step choices100 bits668 plan1100

def plan2288 : Plan := .step choices100 bits668 plan1101

def plan2289 : Plan := .step choices100 bits668 plan1102

def plan2290 : Plan := .step choices100 bits667 plan1103

def plan2291 : Plan := .step choices100 bits667 plan1113

def plan2292 : Plan := .step choices100 bits655 plan1127

def plan2293 : Plan := .step choices100 bits656 plan1128

def plan2294 : Plan := .step choices100 bits656 plan1129

def plan2295 : Plan := .step choices100 bits655 plan1130

def plan2296 : Plan := .step choices100 bits656 plan1131

def plan2297 : Plan := .step choices100 bits666 plan1132

def plan2298 : Plan := .step choices100 bits666 plan1133

def plan2299 : Plan := .step choices100 bits666 plan1134

def plan2300 : Plan := .step choices100 bits665 plan1135

def plan2301 : Plan := .step choices100 bits664 plan1145

def plan2302 : Plan := .step choices100 bits665 plan1149

def plan2303 : Plan := .step choices100 bits668 plan1156

def plan2304 : Plan := .step choices100 bits668 plan1157

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


