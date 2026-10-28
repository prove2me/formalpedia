-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans017
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans017
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:45:37.47719+00:00
-- url     : https://prove2.me/theorems/a05bfe7f-cfe7-4422-b446-66fcfbfbbdbc
-- title:
--   Endpoint22 Reach Plans017 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans017 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1701`, `ThreeBoundEndpoint22Reachable.plan1702`, `ThreeBoundEndpoint22Reachable.plan1703`, `ThreeBoundEndpoint22Reachable.plan1704`, `ThreeBoundEndpoint22Reachable.plan1705`, `ThreeBoundEndpoint22Reachable.plan1706`, `ThreeBoundEndpoint22Reachable.plan1707`, `ThreeBoundEndpoint22Reachable.plan1708`, `ThreeBoundEndpoint22Reachable.plan1709`, `ThreeBoundEndpoint22Reachable.plan1710`, `ThreeBoundEndpoint22Reachable.plan1637`, `ThreeBoundEndpoint22Reachable.plan1711`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans017.lean, lines 1–211.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans009
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
def plan1633 : Plan := .step choices239 bits271 plan597

def plan1634 : Plan := .step choices248 bits421 plan599

def plan1635 : Plan := .step choices248 bits422 plan601

def plan1636 : Plan := .step choices248 bits421 plan602

def plan1637 : Plan := .step choices251 bits332 plan598

def plan1638 : Plan := .step choices251 bits336 plan599

def plan1639 : Plan := .step choices251 bits332 plan600

def plan1640 : Plan := .step choices251 bits337 plan601

def plan1641 : Plan := .step choices251 bits336 plan602

def plan1642 : Plan := .step choices251 bits332 plan603

def plan1643 : Plan := .step choices252 bits338 plan601

def plan1644 : Plan := .step choices255 bits337 plan601

def plan1645 : Plan := .step choices255 bits336 plan602

def plan1646 : Plan := .step choices255 bits332 plan603

def plan1647 : Plan := .step choices259 bits564 plan607

def plan1648 : Plan := .step choices262 bits468 plan604

def plan1649 : Plan := .step choices262 bits469 plan605

def plan1650 : Plan := .step choices262 bits468 plan606

def plan1651 : Plan := .step choices262 bits470 plan607

def plan1652 : Plan := .step choices262 bits469 plan608

def plan1653 : Plan := .step choices262 bits468 plan609

def plan1654 : Plan := .step choices263 bits471 plan607

def plan1655 : Plan := .step choices266 bits470 plan607

def plan1656 : Plan := .step choices266 bits469 plan608

def plan1657 : Plan := .step choices266 bits468 plan609

def plan1658 : Plan := .step choices273 bits633 plan610

def plan1659 : Plan := .step choices273 bits634 plan611

def plan1660 : Plan := .step choices273 bits633 plan612

def plan1661 : Plan := .step choices273 bits635 plan613

def plan1662 : Plan := .step choices273 bits634 plan614

def plan1663 : Plan := .step choices273 bits633 plan615

def plan1664 : Plan := .step choices274 bits636 plan613

def plan1665 : Plan := .step choices277 bits635 plan613

def plan1666 : Plan := .step choices277 bits634 plan614

def plan1667 : Plan := .step choices277 bits633 plan615

def plan1668 : Plan := .step choices284 bits757 plan616

def plan1669 : Plan := .step choices284 bits758 plan617

def plan1670 : Plan := .step choices284 bits757 plan618

def plan1671 : Plan := .step choices284 bits759 plan619

def plan1672 : Plan := .step choices284 bits758 plan620

def plan1673 : Plan := .step choices284 bits757 plan621

def plan1674 : Plan := .step choices285 bits760 plan619

def plan1675 : Plan := .step choices288 bits759 plan619

def plan1676 : Plan := .step choices288 bits758 plan620

def plan1677 : Plan := .step choices288 bits757 plan621

def plan1678 : Plan := .step choices291 bits970 plan622

def plan1679 : Plan := .step choices291 bits971 plan623

def plan1680 : Plan := .step choices291 bits970 plan624

def plan1681 : Plan := .step choices291 bits972 plan625

def plan1682 : Plan := .step choices291 bits971 plan626

def plan1683 : Plan := .step choices291 bits970 plan627

def plan1684 : Plan := .step choices292 bits973 plan625

def plan1685 : Plan := .step choices295 bits972 plan625

def plan1686 : Plan := .step choices295 bits971 plan626

def plan1687 : Plan := .step choices295 bits970 plan627

def plan1688 : Plan := .step choices297 bits472 plan628

def plan1689 : Plan := .step choices301 bits637 plan629

def plan1690 : Plan := .step choices308 bits761 plan630

def plan1691 : Plan := .step choices318 bits974 plan631

def plan1692 : Plan := .step choices325 bits1162 plan632

def plan1693 : Plan := .step choices329 bits1296 plan633

def plan1694 : Plan := .step choices66 bits226 plan905

def plan1695 : Plan := .step choices66 bits227 plan906

def plan1696 : Plan := .step choices66 bits226 plan907

def plan1697 : Plan := .step choices66 bits227 plan908

def plan1698 : Plan := .step choices66 bits228 plan909

def plan1699 : Plan := .step choices66 bits229 plan910

def plan1700 : Plan := .step choices67 bits226 plan903

def plan1701 : Plan := .step choices67 bits226 plan904

def plan1702 : Plan := .step choices67 bits227 plan905

def plan1703 : Plan := .step choices67 bits228 plan906

def plan1704 : Plan := .step choices67 bits227 plan907

def plan1705 : Plan := .step choices67 bits228 plan908

def plan1706 : Plan := .step choices67 bits229 plan909

def plan1707 : Plan := .step choices67 bits230 plan910

def plan1708 : Plan := .step choices68 bits228 plan907

def plan1709 : Plan := .step choices68 bits229 plan908

def plan1710 : Plan := .step choices68 bits230 plan909

def plan1711 : Plan := .step choices68 bits231 plan910

def plan1712 : Plan := .step choices69 bits232 plan910

def plan1713 : Plan := .step choices70 bits347 plan915

def plan1714 : Plan := .step choices70 bits347 plan916

def plan1715 : Plan := .step choices70 bits347 plan918

def plan1716 : Plan := .step choices70 bits349 plan919

def plan1717 : Plan := .step choices70 bits349 plan920

def plan1718 : Plan := .step choices70 bits349 plan921

def plan1719 : Plan := .step choices70 bits346 plan923

def plan1720 : Plan := .step choices70 bits346 plan925

def plan1721 : Plan := .step choices70 bits351 plan928

def plan1722 : Plan := .step choices70 bits355 plan929

def plan1723 : Plan := .step choices70 bits355 plan930

def plan1724 : Plan := .step choices70 bits351 plan931

def plan1725 : Plan := .step choices70 bits355 plan932

def plan1726 : Plan := .step choices70 bits358 plan934

def plan1727 : Plan := .step choices70 bits358 plan935

def plan1728 : Plan := .step choices70 bits358 plan936

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


