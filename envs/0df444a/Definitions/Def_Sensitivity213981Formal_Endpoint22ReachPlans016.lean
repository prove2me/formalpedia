-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans016
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans016
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:45:38.768869+00:00
-- url     : https://prove2.me/theorems/90b6f951-6468-4359-981d-5435d34a2abf
-- title:
--   Endpoint22 Reach Plans016 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans016 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1605`, `ThreeBoundEndpoint22Reachable.plan1606`, `ThreeBoundEndpoint22Reachable.plan1607`, `ThreeBoundEndpoint22Reachable.plan1608`, `ThreeBoundEndpoint22Reachable.plan1541`, `ThreeBoundEndpoint22Reachable.plan1609`, `ThreeBoundEndpoint22Reachable.plan1610`, `ThreeBoundEndpoint22Reachable.plan1611`, `ThreeBoundEndpoint22Reachable.plan1612`, `ThreeBoundEndpoint22Reachable.plan1613`, `ThreeBoundEndpoint22Reachable.plan1614`, `ThreeBoundEndpoint22Reachable.plan1615`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans016.lean, lines 1–208.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
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
def plan1537 : Plan := .step choices194 bits418 plan564

def plan1538 : Plan := .step choices196 bits416 plan557

def plan1539 : Plan := .step choices196 bits330 plan560

def plan1540 : Plan := .step choices196 bits331 plan562

def plan1541 : Plan := .step choices196 bits330 plan563

def plan1542 : Plan := .step choices197 bits332 plan559

def plan1543 : Plan := .step choices197 bits333 plan560

def plan1544 : Plan := .step choices197 bits332 plan561

def plan1545 : Plan := .step choices197 bits334 plan562

def plan1546 : Plan := .step choices197 bits333 plan563

def plan1547 : Plan := .step choices197 bits332 plan564

def plan1548 : Plan := .step choices198 bits335 plan562

def plan1549 : Plan := .step choices200 bits416 plan557

def plan1550 : Plan := .step choices200 bits330 plan560

def plan1551 : Plan := .step choices200 bits331 plan562

def plan1552 : Plan := .step choices200 bits330 plan563

def plan1553 : Plan := .step choices201 bits334 plan562

def plan1554 : Plan := .step choices201 bits333 plan563

def plan1555 : Plan := .step choices201 bits332 plan564

def plan1556 : Plan := .step choices205 bits583 plan565

def plan1557 : Plan := .step choices205 bits584 plan566

def plan1558 : Plan := .step choices205 bits583 plan567

def plan1559 : Plan := .step choices205 bits561 plan568

def plan1560 : Plan := .step choices205 bits562 plan569

def plan1561 : Plan := .step choices205 bits561 plan570

def plan1562 : Plan := .step choices205 bits563 plan571

def plan1563 : Plan := .step choices205 bits562 plan572

def plan1564 : Plan := .step choices205 bits561 plan573

def plan1565 : Plan := .step choices207 bits560 plan566

def plan1566 : Plan := .step choices207 bits462 plan569

def plan1567 : Plan := .step choices207 bits464 plan571

def plan1568 : Plan := .step choices207 bits462 plan572

def plan1569 : Plan := .step choices208 bits463 plan568

def plan1570 : Plan := .step choices208 bits465 plan569

def plan1571 : Plan := .step choices208 bits463 plan570

def plan1572 : Plan := .step choices208 bits466 plan571

def plan1573 : Plan := .step choices208 bits465 plan572

def plan1574 : Plan := .step choices208 bits463 plan573

def plan1575 : Plan := .step choices209 bits467 plan571

def plan1576 : Plan := .step choices211 bits560 plan566

def plan1577 : Plan := .step choices211 bits462 plan569

def plan1578 : Plan := .step choices211 bits464 plan571

def plan1579 : Plan := .step choices211 bits462 plan572

def plan1580 : Plan := .step choices212 bits466 plan571

def plan1581 : Plan := .step choices212 bits465 plan572

def plan1582 : Plan := .step choices212 bits463 plan573

def plan1583 : Plan := .step choices216 bits718 plan575

def plan1584 : Plan := .step choices216 bits719 plan576

def plan1585 : Plan := .step choices216 bits718 plan577

def plan1586 : Plan := .step choices216 bits720 plan578

def plan1587 : Plan := .step choices216 bits719 plan579

def plan1588 : Plan := .step choices216 bits718 plan580

def plan1589 : Plan := .step choices218 bits718 plan574

def plan1590 : Plan := .step choices218 bits629 plan576

def plan1591 : Plan := .step choices218 bits630 plan578

def plan1592 : Plan := .step choices218 bits629 plan579

def plan1593 : Plan := .step choices219 bits629 plan575

def plan1594 : Plan := .step choices219 bits630 plan576

def plan1595 : Plan := .step choices219 bits629 plan577

def plan1596 : Plan := .step choices219 bits631 plan578

def plan1597 : Plan := .step choices219 bits630 plan579

def plan1598 : Plan := .step choices219 bits629 plan580

def plan1599 : Plan := .step choices220 bits632 plan578

def plan1600 : Plan := .step choices222 bits718 plan574

def plan1601 : Plan := .step choices222 bits629 plan576

def plan1602 : Plan := .step choices222 bits630 plan578

def plan1603 : Plan := .step choices222 bits629 plan579

def plan1604 : Plan := .step choices223 bits631 plan578

def plan1605 : Plan := .step choices223 bits630 plan579

def plan1606 : Plan := .step choices223 bits629 plan580

def plan1607 : Plan := .step choices225 bits753 plan582

def plan1608 : Plan := .step choices225 bits754 plan584

def plan1609 : Plan := .step choices225 bits753 plan585

def plan1610 : Plan := .step choices226 bits753 plan581

def plan1611 : Plan := .step choices226 bits754 plan582

def plan1612 : Plan := .step choices226 bits753 plan583

def plan1613 : Plan := .step choices226 bits755 plan584

def plan1614 : Plan := .step choices226 bits754 plan585

def plan1615 : Plan := .step choices226 bits753 plan586

def plan1616 : Plan := .step choices227 bits756 plan584

def plan1617 : Plan := .step choices229 bits753 plan582

def plan1618 : Plan := .step choices229 bits754 plan584

def plan1619 : Plan := .step choices229 bits753 plan585

def plan1620 : Plan := .step choices230 bits755 plan584

def plan1621 : Plan := .step choices230 bits754 plan585

def plan1622 : Plan := .step choices230 bits753 plan586

def plan1623 : Plan := .step choices231 bits135 plan587

def plan1624 : Plan := .step choices233 bits196 plan588

def plan1625 : Plan := .step choices233 bits197 plan589

def plan1626 : Plan := .step choices233 bits196 plan590

def plan1627 : Plan := .step choices239 bits304 plan591

def plan1628 : Plan := .step choices239 bits271 plan592

def plan1629 : Plan := .step choices239 bits272 plan593

def plan1630 : Plan := .step choices239 bits271 plan594

def plan1631 : Plan := .step choices239 bits273 plan595

def plan1632 : Plan := .step choices239 bits272 plan596

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


