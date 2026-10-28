-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans037
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:50:13.648679+00:00
-- url     : https://prove2.me/theorems/0612384c-6205-4537-8da0-710f201eca9f
-- title:
--   Endpoint22 Reach Plans037 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans037 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3620`, `ThreeBoundEndpoint22Reachable.plan3621`, `ThreeBoundEndpoint22Reachable.plan3556`, `ThreeBoundEndpoint22Reachable.plan3622`, `ThreeBoundEndpoint22Reachable.plan3623`, `ThreeBoundEndpoint22Reachable.plan3624`, `ThreeBoundEndpoint22Reachable.plan3625`, `ThreeBoundEndpoint22Reachable.plan3626`, `ThreeBoundEndpoint22Reachable.plan3627`, `ThreeBoundEndpoint22Reachable.plan3628`, `ThreeBoundEndpoint22Reachable.plan3629`, `ThreeBoundEndpoint22Reachable.plan3630`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans037.lean, lines 1–212.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
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
def plan3553 : Plan := .step choices230 bits1288 plan1616

def plan3554 : Plan := .step choices230 bits1287 plan1620

def plan3555 : Plan := .step choices230 bits1286 plan1621

def plan3556 : Plan := .step choices230 bits1285 plan1622

def plan3557 : Plan := .step choices231 bits232 plan1623

def plan3558 : Plan := .step choices233 bits393 plan1624

def plan3559 : Plan := .step choices233 bits394 plan1625

def plan3560 : Plan := .step choices233 bits393 plan1626

def plan3561 : Plan := .step choices239 bits582 plan1627

def plan3562 : Plan := .step choices239 bits546 plan1628

def plan3563 : Plan := .step choices239 bits547 plan1629

def plan3564 : Plan := .step choices239 bits546 plan1630

def plan3565 : Plan := .step choices239 bits548 plan1631

def plan3566 : Plan := .step choices239 bits547 plan1632

def plan3567 : Plan := .step choices239 bits546 plan1633

def plan3568 : Plan := .step choices248 bits748 plan1634

def plan3569 : Plan := .step choices248 bits749 plan1635

def plan3570 : Plan := .step choices248 bits748 plan1636

def plan3571 : Plan := .step choices248 bits714 plan1637

def plan3572 : Plan := .step choices248 bits715 plan1638

def plan3573 : Plan := .step choices248 bits714 plan1639

def plan3574 : Plan := .step choices248 bits716 plan1640

def plan3575 : Plan := .step choices248 bits715 plan1641

def plan3576 : Plan := .step choices248 bits714 plan1642

def plan3577 : Plan := .step choices248 bits717 plan1643

def plan3578 : Plan := .step choices248 bits716 plan1644

def plan3579 : Plan := .step choices248 bits715 plan1645

def plan3580 : Plan := .step choices248 bits714 plan1646

def plan3581 : Plan := .step choices259 bits969 plan1647

def plan3582 : Plan := .step choices259 bits960 plan1649

def plan3583 : Plan := .step choices259 bits961 plan1651

def plan3584 : Plan := .step choices259 bits960 plan1652

def plan3585 : Plan := .step choices259 bits962 plan1654

def plan3586 : Plan := .step choices259 bits961 plan1655

def plan3587 : Plan := .step choices259 bits960 plan1656

def plan3588 : Plan := .step choices262 bits895 plan1648

def plan3589 : Plan := .step choices262 bits896 plan1649

def plan3590 : Plan := .step choices262 bits895 plan1650

def plan3591 : Plan := .step choices262 bits897 plan1651

def plan3592 : Plan := .step choices262 bits896 plan1652

def plan3593 : Plan := .step choices262 bits895 plan1653

def plan3594 : Plan := .step choices262 bits898 plan1654

def plan3595 : Plan := .step choices262 bits897 plan1655

def plan3596 : Plan := .step choices262 bits896 plan1656

def plan3597 : Plan := .step choices262 bits895 plan1657

def plan3598 : Plan := .step choices263 bits899 plan1654

def plan3599 : Plan := .step choices266 bits898 plan1654

def plan3600 : Plan := .step choices266 bits897 plan1655

def plan3601 : Plan := .step choices266 bits896 plan1656

def plan3602 : Plan := .step choices266 bits895 plan1657

def plan3603 : Plan := .step choices270 bits1120 plan1661

def plan3604 : Plan := .step choices270 bits1121 plan1664

def plan3605 : Plan := .step choices270 bits1120 plan1665

def plan3606 : Plan := .step choices273 bits1094 plan1658

def plan3607 : Plan := .step choices273 bits1095 plan1659

def plan3608 : Plan := .step choices273 bits1094 plan1660

def plan3609 : Plan := .step choices273 bits1096 plan1661

def plan3610 : Plan := .step choices273 bits1095 plan1662

def plan3611 : Plan := .step choices273 bits1094 plan1663

def plan3612 : Plan := .step choices273 bits1097 plan1664

def plan3613 : Plan := .step choices273 bits1096 plan1665

def plan3614 : Plan := .step choices273 bits1095 plan1666

def plan3615 : Plan := .step choices273 bits1094 plan1667

def plan3616 : Plan := .step choices274 bits1098 plan1664

def plan3617 : Plan := .step choices277 bits1097 plan1664

def plan3618 : Plan := .step choices277 bits1096 plan1665

def plan3619 : Plan := .step choices277 bits1095 plan1666

def plan3620 : Plan := .step choices277 bits1094 plan1667

def plan3621 : Plan := .step choices281 bits1322 plan1674

def plan3622 : Plan := .step choices284 bits1290 plan1668

def plan3623 : Plan := .step choices284 bits1291 plan1669

def plan3624 : Plan := .step choices284 bits1290 plan1670

def plan3625 : Plan := .step choices284 bits1292 plan1671

def plan3626 : Plan := .step choices284 bits1291 plan1672

def plan3627 : Plan := .step choices284 bits1290 plan1673

def plan3628 : Plan := .step choices284 bits1293 plan1674

def plan3629 : Plan := .step choices284 bits1292 plan1675

def plan3630 : Plan := .step choices284 bits1291 plan1676

def plan3631 : Plan := .step choices284 bits1290 plan1677

def plan3632 : Plan := .step choices285 bits1294 plan1674

def plan3633 : Plan := .step choices288 bits1293 plan1674

def plan3634 : Plan := .step choices288 bits1292 plan1675

def plan3635 : Plan := .step choices288 bits1291 plan1676

def plan3636 : Plan := .step choices288 bits1290 plan1677

def plan3637 : Plan := .step choices291 bits1423 plan1678

def plan3638 : Plan := .step choices291 bits1424 plan1679

def plan3639 : Plan := .step choices291 bits1423 plan1680

def plan3640 : Plan := .step choices291 bits1425 plan1681

def plan3641 : Plan := .step choices291 bits1424 plan1682

def plan3642 : Plan := .step choices291 bits1423 plan1683

def plan3643 : Plan := .step choices291 bits1426 plan1684

def plan3644 : Plan := .step choices291 bits1425 plan1685

def plan3645 : Plan := .step choices291 bits1424 plan1686

def plan3646 : Plan := .step choices291 bits1423 plan1687

def plan3647 : Plan := .step choices292 bits1427 plan1684

def plan3648 : Plan := .step choices295 bits1426 plan1684

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


