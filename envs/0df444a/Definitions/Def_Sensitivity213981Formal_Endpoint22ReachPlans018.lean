-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans018
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans018
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:46:54.319682+00:00
-- url     : https://prove2.me/theorems/ef90b26a-d34c-4593-9fbd-8d8ea43db5a0
-- title:
--   Endpoint22 Reach Plans018 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans018 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1799`, `ThreeBoundEndpoint22Reachable.plan1800`, `ThreeBoundEndpoint22Reachable.plan1801`, `ThreeBoundEndpoint22Reachable.plan1802`, `ThreeBoundEndpoint22Reachable.plan1803`, `ThreeBoundEndpoint22Reachable.plan1804`, `ThreeBoundEndpoint22Reachable.plan1734`, `ThreeBoundEndpoint22Reachable.plan1805`, `ThreeBoundEndpoint22Reachable.plan1806`, `ThreeBoundEndpoint22Reachable.plan1807`, `ThreeBoundEndpoint22Reachable.plan1808`, `ThreeBoundEndpoint22Reachable.plan1809`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans018.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans010
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
def plan1729 : Plan := .step choices70 bits354 plan937

def plan1730 : Plan := .step choices70 bits354 plan938

def plan1731 : Plan := .step choices70 bits360 plan940

def plan1732 : Plan := .step choices70 bits360 plan941

def plan1733 : Plan := .step choices70 bits360 plan942

def plan1734 : Plan := .step choices70 bits350 plan944

def plan1735 : Plan := .step choices70 bits353 plan945

def plan1736 : Plan := .step choices70 bits357 plan946

def plan1737 : Plan := .step choices70 bits350 plan948

def plan1738 : Plan := .step choices70 bits353 plan949

def plan1739 : Plan := .step choices70 bits357 plan950

def plan1740 : Plan := .step choices71 bits348 plan911

def plan1741 : Plan := .step choices71 bits348 plan912

def plan1742 : Plan := .step choices71 bits348 plan913

def plan1743 : Plan := .step choices71 bits352 plan914

def plan1744 : Plan := .step choices71 bits356 plan915

def plan1745 : Plan := .step choices71 bits356 plan916

def plan1746 : Plan := .step choices71 bits352 plan917

def plan1747 : Plan := .step choices71 bits356 plan918

def plan1748 : Plan := .step choices71 bits359 plan919

def plan1749 : Plan := .step choices71 bits359 plan920

def plan1750 : Plan := .step choices71 bits359 plan921

def plan1751 : Plan := .step choices71 bits351 plan922

def plan1752 : Plan := .step choices71 bits355 plan923

def plan1753 : Plan := .step choices71 bits351 plan924

def plan1754 : Plan := .step choices71 bits355 plan925

def plan1755 : Plan := .step choices71 bits363 plan928

def plan1756 : Plan := .step choices71 bits366 plan929

def plan1757 : Plan := .step choices71 bits366 plan930

def plan1758 : Plan := .step choices71 bits363 plan931

def plan1759 : Plan := .step choices71 bits366 plan932

def plan1760 : Plan := .step choices71 bits368 plan934

def plan1761 : Plan := .step choices71 bits368 plan935

def plan1762 : Plan := .step choices71 bits368 plan936

def plan1763 : Plan := .step choices71 bits365 plan937

def plan1764 : Plan := .step choices71 bits365 plan938

def plan1765 : Plan := .step choices71 bits370 plan940

def plan1766 : Plan := .step choices71 bits370 plan941

def plan1767 : Plan := .step choices71 bits370 plan942

def plan1768 : Plan := .step choices71 bits361 plan943

def plan1769 : Plan := .step choices71 bits362 plan944

def plan1770 : Plan := .step choices71 bits364 plan945

def plan1771 : Plan := .step choices71 bits367 plan946

def plan1772 : Plan := .step choices71 bits361 plan947

def plan1773 : Plan := .step choices71 bits362 plan948

def plan1774 : Plan := .step choices71 bits364 plan949

def plan1775 : Plan := .step choices71 bits367 plan950

def plan1776 : Plan := .step choices72 bits373 plan928

def plan1777 : Plan := .step choices72 bits376 plan929

def plan1778 : Plan := .step choices72 bits376 plan930

def plan1779 : Plan := .step choices72 bits373 plan931

def plan1780 : Plan := .step choices72 bits376 plan932

def plan1781 : Plan := .step choices72 bits379 plan934

def plan1782 : Plan := .step choices72 bits379 plan935

def plan1783 : Plan := .step choices72 bits379 plan936

def plan1784 : Plan := .step choices72 bits375 plan937

def plan1785 : Plan := .step choices72 bits375 plan938

def plan1786 : Plan := .step choices72 bits382 plan940

def plan1787 : Plan := .step choices72 bits382 plan941

def plan1788 : Plan := .step choices72 bits382 plan942

def plan1789 : Plan := .step choices72 bits378 plan946

def plan1790 : Plan := .step choices72 bits378 plan950

def plan1791 : Plan := .step choices73 bits383 plan940

def plan1792 : Plan := .step choices73 bits383 plan941

def plan1793 : Plan := .step choices73 bits383 plan942

def plan1794 : Plan := .step choices74 bits371 plan926

def plan1795 : Plan := .step choices74 bits372 plan927

def plan1796 : Plan := .step choices74 bits374 plan933

def plan1797 : Plan := .step choices74 bits377 plan939

def plan1798 : Plan := .step choices75 bits381 plan939

def plan1799 : Plan := .step choices78 bits371 plan926

def plan1800 : Plan := .step choices78 bits372 plan927

def plan1801 : Plan := .step choices78 bits374 plan933

def plan1802 : Plan := .step choices78 bits377 plan939

def plan1803 : Plan := .step choices79 bits381 plan939

def plan1804 : Plan := .step choices81 bits473 plan955

def plan1805 : Plan := .step choices81 bits473 plan956

def plan1806 : Plan := .step choices81 bits473 plan958

def plan1807 : Plan := .step choices81 bits474 plan959

def plan1808 : Plan := .step choices81 bits474 plan960

def plan1809 : Plan := .step choices81 bits474 plan961

def plan1810 : Plan := .step choices81 bits474 plan962

def plan1811 : Plan := .step choices81 bits473 plan966

def plan1812 : Plan := .step choices81 bits473 plan967

def plan1813 : Plan := .step choices81 bits473 plan969

def plan1814 : Plan := .step choices81 bits474 plan970

def plan1815 : Plan := .step choices81 bits474 plan971

def plan1816 : Plan := .step choices81 bits477 plan981

def plan1817 : Plan := .step choices81 bits478 plan982

def plan1818 : Plan := .step choices81 bits478 plan983

def plan1819 : Plan := .step choices81 bits477 plan984

def plan1820 : Plan := .step choices81 bits478 plan985

def plan1821 : Plan := .step choices81 bits479 plan986

def plan1822 : Plan := .step choices81 bits479 plan987

def plan1823 : Plan := .step choices81 bits479 plan988

def plan1824 : Plan := .step choices81 bits479 plan989

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


