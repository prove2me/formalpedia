-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans033
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans033
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:16.379957+00:00
-- url     : https://prove2.me/theorems/964d1a38-cce9-45c2-b8a2-7d61556e050b
-- title:
--   Endpoint22 Reach Plans033 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans033 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3236`, `ThreeBoundEndpoint22Reachable.plan3237`, `ThreeBoundEndpoint22Reachable.plan3238`, `ThreeBoundEndpoint22Reachable.plan3239`, `ThreeBoundEndpoint22Reachable.plan3240`, `ThreeBoundEndpoint22Reachable.plan3241`, `ThreeBoundEndpoint22Reachable.plan3242`, `ThreeBoundEndpoint22Reachable.plan3243`, `ThreeBoundEndpoint22Reachable.plan3244`, `ThreeBoundEndpoint22Reachable.plan3245`, `ThreeBoundEndpoint22Reachable.plan3174`, `ThreeBoundEndpoint22Reachable.plan3246`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans033.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
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
def plan3169 : Plan := .step choices159 bits1081 plan1498

def plan3170 : Plan := .step choices159 bits1079 plan1499

def plan3171 : Plan := .step choices159 bits1080 plan1500

def plan3172 : Plan := .step choices159 bits1082 plan1501

def plan3173 : Plan := .step choices159 bits1081 plan1502

def plan3174 : Plan := .step choices159 bits1084 plan1503

def plan3175 : Plan := .step choices159 bits1083 plan1504

def plan3176 : Plan := .step choices159 bits1082 plan1505

def plan3177 : Plan := .step choices160 bits1083 plan1483

def plan3178 : Plan := .step choices160 bits1084 plan1484

def plan3179 : Plan := .step choices160 bits1083 plan1485

def plan3180 : Plan := .step choices160 bits1085 plan1486

def plan3181 : Plan := .step choices160 bits1084 plan1487

def plan3182 : Plan := .step choices160 bits1083 plan1488

def plan3183 : Plan := .step choices160 bits1086 plan1489

def plan3184 : Plan := .step choices160 bits1085 plan1503

def plan3185 : Plan := .step choices160 bits1084 plan1504

def plan3186 : Plan := .step choices160 bits1083 plan1505

def plan3187 : Plan := .step choices161 bits1087 plan1489

def plan3188 : Plan := .step choices162 bits1080 plan1470

def plan3189 : Plan := .step choices162 bits1080 plan1473

def plan3190 : Plan := .step choices162 bits1081 plan1474

def plan3191 : Plan := .step choices162 bits1080 plan1475

def plan3192 : Plan := .step choices162 bits1082 plan1476

def plan3193 : Plan := .step choices162 bits1080 plan1478

def plan3194 : Plan := .step choices162 bits1081 plan1481

def plan3195 : Plan := .step choices162 bits1080 plan1482

def plan3196 : Plan := .step choices162 bits1081 plan1483

def plan3197 : Plan := .step choices162 bits1082 plan1484

def plan3198 : Plan := .step choices162 bits1081 plan1485

def plan3199 : Plan := .step choices162 bits1083 plan1486

def plan3200 : Plan := .step choices162 bits1082 plan1487

def plan3201 : Plan := .step choices162 bits1081 plan1488

def plan3202 : Plan := .step choices162 bits1084 plan1489

def plan3203 : Plan := .step choices162 bits1080 plan1490

def plan3204 : Plan := .step choices162 bits1081 plan1491

def plan3205 : Plan := .step choices162 bits1080 plan1492

def plan3206 : Plan := .step choices162 bits1080 plan1493

def plan3207 : Plan := .step choices162 bits1081 plan1494

def plan3208 : Plan := .step choices162 bits1080 plan1495

def plan3209 : Plan := .step choices162 bits1082 plan1496

def plan3210 : Plan := .step choices162 bits1080 plan1498

def plan3211 : Plan := .step choices162 bits1081 plan1501

def plan3212 : Plan := .step choices162 bits1080 plan1502

def plan3213 : Plan := .step choices162 bits1083 plan1503

def plan3214 : Plan := .step choices162 bits1082 plan1504

def plan3215 : Plan := .step choices162 bits1081 plan1505

def plan3216 : Plan := .step choices163 bits1082 plan1483

def plan3217 : Plan := .step choices163 bits1083 plan1484

def plan3218 : Plan := .step choices163 bits1082 plan1485

def plan3219 : Plan := .step choices163 bits1084 plan1486

def plan3220 : Plan := .step choices163 bits1083 plan1487

def plan3221 : Plan := .step choices163 bits1082 plan1488

def plan3222 : Plan := .step choices163 bits1085 plan1489

def plan3223 : Plan := .step choices163 bits1081 plan1493

def plan3224 : Plan := .step choices163 bits1082 plan1494

def plan3225 : Plan := .step choices163 bits1081 plan1495

def plan3226 : Plan := .step choices163 bits1083 plan1496

def plan3227 : Plan := .step choices163 bits1080 plan1497

def plan3228 : Plan := .step choices163 bits1081 plan1498

def plan3229 : Plan := .step choices163 bits1079 plan1499

def plan3230 : Plan := .step choices163 bits1080 plan1500

def plan3231 : Plan := .step choices163 bits1082 plan1501

def plan3232 : Plan := .step choices163 bits1081 plan1502

def plan3233 : Plan := .step choices163 bits1084 plan1503

def plan3234 : Plan := .step choices163 bits1083 plan1504

def plan3235 : Plan := .step choices163 bits1082 plan1505

def plan3236 : Plan := .step choices164 bits1086 plan1489

def plan3237 : Plan := .step choices164 bits1085 plan1503

def plan3238 : Plan := .step choices164 bits1084 plan1504

def plan3239 : Plan := .step choices164 bits1083 plan1505

def plan3240 : Plan := .step choices167 bits231 plan1506

def plan3241 : Plan := .step choices168 bits232 plan1506

def plan3242 : Plan := .step choices171 bits386 plan1507

def plan3243 : Plan := .step choices171 bits389 plan1509

def plan3244 : Plan := .step choices171 bits390 plan1510

def plan3245 : Plan := .step choices171 bits389 plan1511

def plan3246 : Plan := .step choices172 bits429 plan1508

def plan3247 : Plan := .step choices172 bits393 plan1509

def plan3248 : Plan := .step choices172 bits394 plan1510

def plan3249 : Plan := .step choices172 bits393 plan1511

def plan3250 : Plan := .step choices174 bits392 plan1508

def plan3251 : Plan := .step choices178 bits392 plan1508

def plan3252 : Plan := .step choices182 bits534 plan1512

def plan3253 : Plan := .step choices182 bits539 plan1513

def plan3254 : Plan := .step choices182 bits534 plan1514

def plan3255 : Plan := .step choices182 bits579 plan1517

def plan3256 : Plan := .step choices182 bits542 plan1519

def plan3257 : Plan := .step choices182 bits543 plan1520

def plan3258 : Plan := .step choices182 bits542 plan1521

def plan3259 : Plan := .step choices182 bits544 plan1522

def plan3260 : Plan := .step choices182 bits543 plan1523

def plan3261 : Plan := .step choices182 bits542 plan1524

def plan3262 : Plan := .step choices182 bits542 plan1525

def plan3263 : Plan := .step choices182 bits542 plan1526

def plan3264 : Plan := .step choices183 bits613 plan1515

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


