-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans034
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans034
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:55.115284+00:00
-- url     : https://prove2.me/theorems/4c417156-6752-43a4-95a7-5c772c705192
-- title:
--   Endpoint22 Reach Plans034 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans034 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3333`, `ThreeBoundEndpoint22Reachable.plan3334`, `ThreeBoundEndpoint22Reachable.plan3335`, `ThreeBoundEndpoint22Reachable.plan3336`, `ThreeBoundEndpoint22Reachable.plan3337`, `ThreeBoundEndpoint22Reachable.plan3338`, `ThreeBoundEndpoint22Reachable.plan3339`, `ThreeBoundEndpoint22Reachable.plan3340`, `ThreeBoundEndpoint22Reachable.plan3341`, `ThreeBoundEndpoint22Reachable.plan3270`, `ThreeBoundEndpoint22Reachable.plan3342`, `ThreeBoundEndpoint22Reachable.plan3343`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans034.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
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
def plan3265 : Plan := .step choices183 bits581 plan1516

def plan3266 : Plan := .step choices183 bits582 plan1517

def plan3267 : Plan := .step choices183 bits581 plan1518

def plan3268 : Plan := .step choices183 bits546 plan1519

def plan3269 : Plan := .step choices183 bits547 plan1520

def plan3270 : Plan := .step choices183 bits546 plan1521

def plan3271 : Plan := .step choices183 bits548 plan1522

def plan3272 : Plan := .step choices183 bits547 plan1523

def plan3273 : Plan := .step choices183 bits546 plan1524

def plan3274 : Plan := .step choices185 bits580 plan1515

def plan3275 : Plan := .step choices185 bits545 plan1516

def plan3276 : Plan := .step choices185 bits546 plan1517

def plan3277 : Plan := .step choices185 bits545 plan1518

def plan3278 : Plan := .step choices189 bits580 plan1515

def plan3279 : Plan := .step choices189 bits545 plan1516

def plan3280 : Plan := .step choices189 bits546 plan1517

def plan3281 : Plan := .step choices189 bits545 plan1518

def plan3282 : Plan := .step choices192 bits703 plan1548

def plan3283 : Plan := .step choices193 bits741 plan1527

def plan3284 : Plan := .step choices193 bits743 plan1533

def plan3285 : Plan := .step choices193 bits744 plan1535

def plan3286 : Plan := .step choices193 bits743 plan1536

def plan3287 : Plan := .step choices193 bits704 plan1539

def plan3288 : Plan := .step choices193 bits705 plan1540

def plan3289 : Plan := .step choices193 bits704 plan1541

def plan3290 : Plan := .step choices193 bits706 plan1542

def plan3291 : Plan := .step choices193 bits707 plan1543

def plan3292 : Plan := .step choices193 bits706 plan1544

def plan3293 : Plan := .step choices193 bits708 plan1545

def plan3294 : Plan := .step choices193 bits707 plan1546

def plan3295 : Plan := .step choices193 bits706 plan1547

def plan3296 : Plan := .step choices193 bits709 plan1548

def plan3297 : Plan := .step choices193 bits704 plan1550

def plan3298 : Plan := .step choices193 bits705 plan1551

def plan3299 : Plan := .step choices193 bits704 plan1552

def plan3300 : Plan := .step choices193 bits708 plan1553

def plan3301 : Plan := .step choices193 bits707 plan1554

def plan3302 : Plan := .step choices193 bits706 plan1555

def plan3303 : Plan := .step choices194 bits751 plan1529

def plan3304 : Plan := .step choices194 bits752 plan1530

def plan3305 : Plan := .step choices194 bits751 plan1531

def plan3306 : Plan := .step choices194 bits745 plan1532

def plan3307 : Plan := .step choices194 bits746 plan1533

def plan3308 : Plan := .step choices194 bits745 plan1534

def plan3309 : Plan := .step choices194 bits747 plan1535

def plan3310 : Plan := .step choices194 bits746 plan1536

def plan3311 : Plan := .step choices194 bits745 plan1537

def plan3312 : Plan := .step choices194 bits710 plan1542

def plan3313 : Plan := .step choices194 bits711 plan1543

def plan3314 : Plan := .step choices194 bits710 plan1544

def plan3315 : Plan := .step choices194 bits712 plan1545

def plan3316 : Plan := .step choices194 bits711 plan1546

def plan3317 : Plan := .step choices194 bits710 plan1547

def plan3318 : Plan := .step choices194 bits713 plan1548

def plan3319 : Plan := .step choices194 bits712 plan1553

def plan3320 : Plan := .step choices194 bits711 plan1554

def plan3321 : Plan := .step choices194 bits710 plan1555

def plan3322 : Plan := .step choices196 bits750 plan1528

def plan3323 : Plan := .step choices196 bits742 plan1529

def plan3324 : Plan := .step choices196 bits743 plan1530

def plan3325 : Plan := .step choices196 bits742 plan1531

def plan3326 : Plan := .step choices196 bits706 plan1532

def plan3327 : Plan := .step choices196 bits707 plan1533

def plan3328 : Plan := .step choices196 bits706 plan1534

def plan3329 : Plan := .step choices196 bits708 plan1535

def plan3330 : Plan := .step choices196 bits707 plan1536

def plan3331 : Plan := .step choices196 bits706 plan1537

def plan3332 : Plan := .step choices196 bits704 plan1538

def plan3333 : Plan := .step choices196 bits704 plan1549

def plan3334 : Plan := .step choices200 bits750 plan1528

def plan3335 : Plan := .step choices200 bits742 plan1529

def plan3336 : Plan := .step choices200 bits743 plan1530

def plan3337 : Plan := .step choices200 bits742 plan1531

def plan3338 : Plan := .step choices200 bits706 plan1532

def plan3339 : Plan := .step choices200 bits707 plan1533

def plan3340 : Plan := .step choices200 bits706 plan1534

def plan3341 : Plan := .step choices200 bits708 plan1535

def plan3342 : Plan := .step choices200 bits707 plan1536

def plan3343 : Plan := .step choices200 bits706 plan1537

def plan3344 : Plan := .step choices200 bits704 plan1549

def plan3345 : Plan := .step choices204 bits963 plan1562

def plan3346 : Plan := .step choices204 bits948 plan1567

def plan3347 : Plan := .step choices204 bits949 plan1570

def plan3348 : Plan := .step choices204 bits950 plan1572

def plan3349 : Plan := .step choices204 bits949 plan1573

def plan3350 : Plan := .step choices204 bits951 plan1575

def plan3351 : Plan := .step choices204 bits948 plan1578

def plan3352 : Plan := .step choices204 bits950 plan1580

def plan3353 : Plan := .step choices204 bits949 plan1581

def plan3354 : Plan := .step choices205 bits966 plan1559

def plan3355 : Plan := .step choices205 bits967 plan1560

def plan3356 : Plan := .step choices205 bits966 plan1561

def plan3357 : Plan := .step choices205 bits968 plan1562

def plan3358 : Plan := .step choices205 bits967 plan1563

def plan3359 : Plan := .step choices205 bits966 plan1564

def plan3360 : Plan := .step choices205 bits955 plan1569

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


