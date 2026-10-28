-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans020
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans020
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:30.625774+00:00
-- url     : https://prove2.me/theorems/f75a8145-3ee4-42b5-9dfc-7e2f0a91a025
-- title:
--   Endpoint22 Reach Plans020 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans020 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1990`, `ThreeBoundEndpoint22Reachable.plan1991`, `ThreeBoundEndpoint22Reachable.plan1992`, `ThreeBoundEndpoint22Reachable.plan1926`, `ThreeBoundEndpoint22Reachable.plan1993`, `ThreeBoundEndpoint22Reachable.plan1994`, `ThreeBoundEndpoint22Reachable.plan1995`, `ThreeBoundEndpoint22Reachable.plan1996`, `ThreeBoundEndpoint22Reachable.plan1997`, `ThreeBoundEndpoint22Reachable.plan1998`, `ThreeBoundEndpoint22Reachable.plan1999`, `ThreeBoundEndpoint22Reachable.plan2000`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans020.lean, lines 1–203.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
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
def plan1921 : Plan := .step choices82 bits485 plan1029

def plan1922 : Plan := .step choices82 bits486 plan1030

def plan1923 : Plan := .step choices82 bits486 plan1031

def plan1924 : Plan := .step choices82 bits485 plan1032

def plan1925 : Plan := .step choices82 bits486 plan1033

def plan1926 : Plan := .step choices82 bits489 plan1035

def plan1927 : Plan := .step choices82 bits489 plan1036

def plan1928 : Plan := .step choices82 bits489 plan1037

def plan1929 : Plan := .step choices82 bits488 plan1038

def plan1930 : Plan := .step choices82 bits484 plan1039

def plan1931 : Plan := .step choices82 bits488 plan1040

def plan1932 : Plan := .step choices82 bits495 plan1042

def plan1933 : Plan := .step choices82 bits495 plan1043

def plan1934 : Plan := .step choices82 bits495 plan1044

def plan1935 : Plan := .step choices82 bits494 plan1045

def plan1936 : Plan := .step choices83 bits497 plan981

def plan1937 : Plan := .step choices83 bits498 plan982

def plan1938 : Plan := .step choices83 bits498 plan983

def plan1939 : Plan := .step choices83 bits497 plan984

def plan1940 : Plan := .step choices83 bits498 plan985

def plan1941 : Plan := .step choices83 bits499 plan986

def plan1942 : Plan := .step choices83 bits499 plan987

def plan1943 : Plan := .step choices83 bits499 plan988

def plan1944 : Plan := .step choices83 bits499 plan989

def plan1945 : Plan := .step choices83 bits498 plan991

def plan1946 : Plan := .step choices83 bits498 plan992

def plan1947 : Plan := .step choices83 bits497 plan993

def plan1948 : Plan := .step choices83 bits498 plan994

def plan1949 : Plan := .step choices83 bits499 plan995

def plan1950 : Plan := .step choices83 bits499 plan996

def plan1951 : Plan := .step choices83 bits504 plan1000

def plan1952 : Plan := .step choices83 bits504 plan1001

def plan1953 : Plan := .step choices83 bits504 plan1002

def plan1954 : Plan := .step choices83 bits504 plan1003

def plan1955 : Plan := .step choices83 bits504 plan1004

def plan1956 : Plan := .step choices83 bits504 plan1005

def plan1957 : Plan := .step choices83 bits503 plan1022

def plan1958 : Plan := .step choices83 bits503 plan1023

def plan1959 : Plan := .step choices83 bits503 plan1024

def plan1960 : Plan := .step choices83 bits502 plan1025

def plan1961 : Plan := .step choices83 bits502 plan1026

def plan1962 : Plan := .step choices83 bits503 plan1042

def plan1963 : Plan := .step choices83 bits503 plan1043

def plan1964 : Plan := .step choices83 bits503 plan1044

def plan1965 : Plan := .step choices83 bits502 plan1045

def plan1966 : Plan := .step choices84 bits507 plan1000

def plan1967 : Plan := .step choices84 bits507 plan1001

def plan1968 : Plan := .step choices84 bits507 plan1002

def plan1969 : Plan := .step choices84 bits507 plan1003

def plan1970 : Plan := .step choices84 bits507 plan1004

def plan1971 : Plan := .step choices84 bits507 plan1005

def plan1972 : Plan := .step choices85 bits490 plan972

def plan1973 : Plan := .step choices85 bits491 plan973

def plan1974 : Plan := .step choices85 bits491 plan974

def plan1975 : Plan := .step choices85 bits490 plan975

def plan1976 : Plan := .step choices85 bits491 plan976

def plan1977 : Plan := .step choices85 bits495 plan977

def plan1978 : Plan := .step choices85 bits495 plan978

def plan1979 : Plan := .step choices85 bits495 plan979

def plan1980 : Plan := .step choices85 bits494 plan980

def plan1981 : Plan := .step choices85 bits494 plan990

def plan1982 : Plan := .step choices85 bits501 plan997

def plan1983 : Plan := .step choices85 bits501 plan998

def plan1984 : Plan := .step choices85 bits501 plan999

def plan1985 : Plan := .step choices85 bits485 plan1006

def plan1986 : Plan := .step choices85 bits488 plan1007

def plan1987 : Plan := .step choices85 bits493 plan1013

def plan1988 : Plan := .step choices85 bits500 plan1021

def plan1989 : Plan := .step choices85 bits485 plan1027

def plan1990 : Plan := .step choices85 bits488 plan1028

def plan1991 : Plan := .step choices85 bits493 plan1034

def plan1992 : Plan := .step choices85 bits500 plan1041

def plan1993 : Plan := .step choices86 bits506 plan997

def plan1994 : Plan := .step choices86 bits506 plan998

def plan1995 : Plan := .step choices86 bits506 plan999

def plan1996 : Plan := .step choices86 bits505 plan1021

def plan1997 : Plan := .step choices86 bits505 plan1041

def plan1998 : Plan := .step choices89 bits490 plan972

def plan1999 : Plan := .step choices89 bits491 plan973

def plan2000 : Plan := .step choices89 bits491 plan974

def plan2001 : Plan := .step choices89 bits490 plan975

def plan2002 : Plan := .step choices89 bits491 plan976

def plan2003 : Plan := .step choices89 bits495 plan977

def plan2004 : Plan := .step choices89 bits495 plan978

def plan2005 : Plan := .step choices89 bits495 plan979

def plan2006 : Plan := .step choices89 bits494 plan980

def plan2007 : Plan := .step choices89 bits494 plan990

def plan2008 : Plan := .step choices89 bits501 plan997

def plan2009 : Plan := .step choices89 bits501 plan998

def plan2010 : Plan := .step choices89 bits501 plan999

def plan2011 : Plan := .step choices89 bits500 plan1021

def plan2012 : Plan := .step choices89 bits485 plan1027

def plan2013 : Plan := .step choices89 bits488 plan1028

def plan2014 : Plan := .step choices89 bits493 plan1034

def plan2015 : Plan := .step choices89 bits500 plan1041

def plan2016 : Plan := .step choices90 bits506 plan997

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


