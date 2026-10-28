-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans036
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:46:27.180643+00:00
-- url     : https://prove2.me/theorems/253b6c1f-441c-4fd3-8ce7-c448d60cfbd0
-- title:
--   Endpoint22 Reach Plans036 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans036 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3525`, `ThreeBoundEndpoint22Reachable.plan3526`, `ThreeBoundEndpoint22Reachable.plan3527`, `ThreeBoundEndpoint22Reachable.plan3528`, `ThreeBoundEndpoint22Reachable.plan3529`, `ThreeBoundEndpoint22Reachable.plan3462`, `ThreeBoundEndpoint22Reachable.plan3530`, `ThreeBoundEndpoint22Reachable.plan3531`, `ThreeBoundEndpoint22Reachable.plan3532`, `ThreeBoundEndpoint22Reachable.plan3533`, `ThreeBoundEndpoint22Reachable.plan3534`, `ThreeBoundEndpoint22Reachable.plan3535`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans036.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
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
def plan3457 : Plan := .step choices218 bits1115 plan1589

def plan3458 : Plan := .step choices218 bits1088 plan1590

def plan3459 : Plan := .step choices218 bits1089 plan1591

def plan3460 : Plan := .step choices218 bits1088 plan1592

def plan3461 : Plan := .step choices218 bits1088 plan1593

def plan3462 : Plan := .step choices218 bits1089 plan1594

def plan3463 : Plan := .step choices218 bits1088 plan1595

def plan3464 : Plan := .step choices218 bits1090 plan1596

def plan3465 : Plan := .step choices218 bits1089 plan1597

def plan3466 : Plan := .step choices218 bits1088 plan1598

def plan3467 : Plan := .step choices218 bits1091 plan1599

def plan3468 : Plan := .step choices218 bits1115 plan1600

def plan3469 : Plan := .step choices218 bits1088 plan1601

def plan3470 : Plan := .step choices218 bits1089 plan1602

def plan3471 : Plan := .step choices218 bits1088 plan1603

def plan3472 : Plan := .step choices218 bits1090 plan1604

def plan3473 : Plan := .step choices218 bits1089 plan1605

def plan3474 : Plan := .step choices218 bits1088 plan1606

def plan3475 : Plan := .step choices219 bits1089 plan1593

def plan3476 : Plan := .step choices219 bits1090 plan1594

def plan3477 : Plan := .step choices219 bits1089 plan1595

def plan3478 : Plan := .step choices219 bits1091 plan1596

def plan3479 : Plan := .step choices219 bits1090 plan1597

def plan3480 : Plan := .step choices219 bits1089 plan1598

def plan3481 : Plan := .step choices219 bits1092 plan1599

def plan3482 : Plan := .step choices219 bits1091 plan1604

def plan3483 : Plan := .step choices219 bits1090 plan1605

def plan3484 : Plan := .step choices219 bits1089 plan1606

def plan3485 : Plan := .step choices220 bits1093 plan1599

def plan3486 : Plan := .step choices221 bits1090 plan1599

def plan3487 : Plan := .step choices222 bits1115 plan1583

def plan3488 : Plan := .step choices222 bits1116 plan1584

def plan3489 : Plan := .step choices222 bits1115 plan1585

def plan3490 : Plan := .step choices222 bits1117 plan1586

def plan3491 : Plan := .step choices222 bits1116 plan1587

def plan3492 : Plan := .step choices222 bits1115 plan1588

def plan3493 : Plan := .step choices222 bits1088 plan1593

def plan3494 : Plan := .step choices222 bits1089 plan1594

def plan3495 : Plan := .step choices222 bits1088 plan1595

def plan3496 : Plan := .step choices222 bits1090 plan1596

def plan3497 : Plan := .step choices222 bits1089 plan1597

def plan3498 : Plan := .step choices222 bits1088 plan1598

def plan3499 : Plan := .step choices222 bits1091 plan1599

def plan3500 : Plan := .step choices222 bits1115 plan1600

def plan3501 : Plan := .step choices222 bits1088 plan1601

def plan3502 : Plan := .step choices222 bits1089 plan1602

def plan3503 : Plan := .step choices222 bits1088 plan1603

def plan3504 : Plan := .step choices222 bits1090 plan1604

def plan3505 : Plan := .step choices222 bits1089 plan1605

def plan3506 : Plan := .step choices222 bits1088 plan1606

def plan3507 : Plan := .step choices223 bits1092 plan1599

def plan3508 : Plan := .step choices223 bits1091 plan1604

def plan3509 : Plan := .step choices223 bits1090 plan1605

def plan3510 : Plan := .step choices223 bits1089 plan1606

def plan3511 : Plan := .step choices224 bits1286 plan1616

def plan3512 : Plan := .step choices225 bits1284 plan1607

def plan3513 : Plan := .step choices225 bits1285 plan1608

def plan3514 : Plan := .step choices225 bits1284 plan1609

def plan3515 : Plan := .step choices225 bits1284 plan1610

def plan3516 : Plan := .step choices225 bits1285 plan1611

def plan3517 : Plan := .step choices225 bits1284 plan1612

def plan3518 : Plan := .step choices225 bits1286 plan1613

def plan3519 : Plan := .step choices225 bits1285 plan1614

def plan3520 : Plan := .step choices225 bits1284 plan1615

def plan3521 : Plan := .step choices225 bits1287 plan1616

def plan3522 : Plan := .step choices225 bits1284 plan1617

def plan3523 : Plan := .step choices225 bits1285 plan1618

def plan3524 : Plan := .step choices225 bits1284 plan1619

def plan3525 : Plan := .step choices225 bits1286 plan1620

def plan3526 : Plan := .step choices225 bits1285 plan1621

def plan3527 : Plan := .step choices225 bits1284 plan1622

def plan3528 : Plan := .step choices226 bits1285 plan1610

def plan3529 : Plan := .step choices226 bits1286 plan1611

def plan3530 : Plan := .step choices226 bits1285 plan1612

def plan3531 : Plan := .step choices226 bits1287 plan1613

def plan3532 : Plan := .step choices226 bits1286 plan1614

def plan3533 : Plan := .step choices226 bits1285 plan1615

def plan3534 : Plan := .step choices226 bits1288 plan1616

def plan3535 : Plan := .step choices226 bits1287 plan1620

def plan3536 : Plan := .step choices226 bits1286 plan1621

def plan3537 : Plan := .step choices226 bits1285 plan1622

def plan3538 : Plan := .step choices227 bits1289 plan1616

def plan3539 : Plan := .step choices228 bits1286 plan1616

def plan3540 : Plan := .step choices229 bits1284 plan1610

def plan3541 : Plan := .step choices229 bits1285 plan1611

def plan3542 : Plan := .step choices229 bits1284 plan1612

def plan3543 : Plan := .step choices229 bits1286 plan1613

def plan3544 : Plan := .step choices229 bits1285 plan1614

def plan3545 : Plan := .step choices229 bits1284 plan1615

def plan3546 : Plan := .step choices229 bits1287 plan1616

def plan3547 : Plan := .step choices229 bits1284 plan1617

def plan3548 : Plan := .step choices229 bits1285 plan1618

def plan3549 : Plan := .step choices229 bits1284 plan1619

def plan3550 : Plan := .step choices229 bits1286 plan1620

def plan3551 : Plan := .step choices229 bits1285 plan1621

def plan3552 : Plan := .step choices229 bits1284 plan1622

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


