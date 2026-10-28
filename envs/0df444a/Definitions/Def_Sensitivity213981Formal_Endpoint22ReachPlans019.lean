-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans019
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans019
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:00.249203+00:00
-- url     : https://prove2.me/theorems/62790af0-bf88-4956-bdc3-f53e80ce64cc
-- title:
--   Endpoint22 Reach Plans019 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans019 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1894`, `ThreeBoundEndpoint22Reachable.plan1895`, `ThreeBoundEndpoint22Reachable.plan1896`, `ThreeBoundEndpoint22Reachable.plan1897`, `ThreeBoundEndpoint22Reachable.plan1898`, `ThreeBoundEndpoint22Reachable.plan1830`, `ThreeBoundEndpoint22Reachable.plan1899`, `ThreeBoundEndpoint22Reachable.plan1900`, `ThreeBoundEndpoint22Reachable.plan1901`, `ThreeBoundEndpoint22Reachable.plan1902`, `ThreeBoundEndpoint22Reachable.plan1903`, `ThreeBoundEndpoint22Reachable.plan1904`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans019.lean, lines 1–204.

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
def plan1825 : Plan := .step choices81 bits478 plan991

def plan1826 : Plan := .step choices81 bits478 plan992

def plan1827 : Plan := .step choices81 bits477 plan993

def plan1828 : Plan := .step choices81 bits478 plan994

def plan1829 : Plan := .step choices81 bits479 plan995

def plan1830 : Plan := .step choices81 bits479 plan996

def plan1831 : Plan := .step choices81 bits482 plan1000

def plan1832 : Plan := .step choices81 bits482 plan1001

def plan1833 : Plan := .step choices81 bits482 plan1002

def plan1834 : Plan := .step choices81 bits482 plan1003

def plan1835 : Plan := .step choices81 bits482 plan1004

def plan1836 : Plan := .step choices81 bits482 plan1005

def plan1837 : Plan := .step choices81 bits473 plan1009

def plan1838 : Plan := .step choices81 bits473 plan1010

def plan1839 : Plan := .step choices81 bits473 plan1012

def plan1840 : Plan := .step choices81 bits476 plan1014

def plan1841 : Plan := .step choices81 bits476 plan1015

def plan1842 : Plan := .step choices81 bits476 plan1016

def plan1843 : Plan := .step choices81 bits475 plan1018

def plan1844 : Plan := .step choices81 bits475 plan1020

def plan1845 : Plan := .step choices81 bits481 plan1022

def plan1846 : Plan := .step choices81 bits481 plan1023

def plan1847 : Plan := .step choices81 bits481 plan1024

def plan1848 : Plan := .step choices81 bits480 plan1025

def plan1849 : Plan := .step choices81 bits480 plan1026

def plan1850 : Plan := .step choices81 bits473 plan1030

def plan1851 : Plan := .step choices81 bits473 plan1031

def plan1852 : Plan := .step choices81 bits473 plan1033

def plan1853 : Plan := .step choices81 bits476 plan1035

def plan1854 : Plan := .step choices81 bits476 plan1036

def plan1855 : Plan := .step choices81 bits476 plan1037

def plan1856 : Plan := .step choices81 bits475 plan1038

def plan1857 : Plan := .step choices81 bits475 plan1040

def plan1858 : Plan := .step choices81 bits481 plan1042

def plan1859 : Plan := .step choices81 bits481 plan1043

def plan1860 : Plan := .step choices81 bits481 plan1044

def plan1861 : Plan := .step choices81 bits480 plan1045

def plan1862 : Plan := .step choices82 bits483 plan951

def plan1863 : Plan := .step choices82 bits483 plan952

def plan1864 : Plan := .step choices82 bits483 plan953

def plan1865 : Plan := .step choices82 bits485 plan954

def plan1866 : Plan := .step choices82 bits486 plan955

def plan1867 : Plan := .step choices82 bits486 plan956

def plan1868 : Plan := .step choices82 bits485 plan957

def plan1869 : Plan := .step choices82 bits486 plan958

def plan1870 : Plan := .step choices82 bits487 plan959

def plan1871 : Plan := .step choices82 bits487 plan960

def plan1872 : Plan := .step choices82 bits487 plan961

def plan1873 : Plan := .step choices82 bits487 plan962

def plan1874 : Plan := .step choices82 bits483 plan963

def plan1875 : Plan := .step choices82 bits483 plan964

def plan1876 : Plan := .step choices82 bits483 plan965

def plan1877 : Plan := .step choices82 bits486 plan966

def plan1878 : Plan := .step choices82 bits486 plan967

def plan1879 : Plan := .step choices82 bits485 plan968

def plan1880 : Plan := .step choices82 bits486 plan969

def plan1881 : Plan := .step choices82 bits487 plan970

def plan1882 : Plan := .step choices82 bits487 plan971

def plan1883 : Plan := .step choices82 bits490 plan981

def plan1884 : Plan := .step choices82 bits491 plan982

def plan1885 : Plan := .step choices82 bits491 plan983

def plan1886 : Plan := .step choices82 bits490 plan984

def plan1887 : Plan := .step choices82 bits491 plan985

def plan1888 : Plan := .step choices82 bits492 plan986

def plan1889 : Plan := .step choices82 bits492 plan987

def plan1890 : Plan := .step choices82 bits492 plan988

def plan1891 : Plan := .step choices82 bits492 plan989

def plan1892 : Plan := .step choices82 bits491 plan991

def plan1893 : Plan := .step choices82 bits491 plan992

def plan1894 : Plan := .step choices82 bits490 plan993

def plan1895 : Plan := .step choices82 bits491 plan994

def plan1896 : Plan := .step choices82 bits492 plan995

def plan1897 : Plan := .step choices82 bits492 plan996

def plan1898 : Plan := .step choices82 bits496 plan1000

def plan1899 : Plan := .step choices82 bits496 plan1001

def plan1900 : Plan := .step choices82 bits496 plan1002

def plan1901 : Plan := .step choices82 bits496 plan1003

def plan1902 : Plan := .step choices82 bits496 plan1004

def plan1903 : Plan := .step choices82 bits496 plan1005

def plan1904 : Plan := .step choices82 bits485 plan1008

def plan1905 : Plan := .step choices82 bits486 plan1009

def plan1906 : Plan := .step choices82 bits486 plan1010

def plan1907 : Plan := .step choices82 bits485 plan1011

def plan1908 : Plan := .step choices82 bits486 plan1012

def plan1909 : Plan := .step choices82 bits489 plan1014

def plan1910 : Plan := .step choices82 bits489 plan1015

def plan1911 : Plan := .step choices82 bits489 plan1016

def plan1912 : Plan := .step choices82 bits484 plan1017

def plan1913 : Plan := .step choices82 bits488 plan1018

def plan1914 : Plan := .step choices82 bits484 plan1019

def plan1915 : Plan := .step choices82 bits488 plan1020

def plan1916 : Plan := .step choices82 bits495 plan1022

def plan1917 : Plan := .step choices82 bits495 plan1023

def plan1918 : Plan := .step choices82 bits495 plan1024

def plan1919 : Plan := .step choices82 bits494 plan1025

def plan1920 : Plan := .step choices82 bits494 plan1026

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


