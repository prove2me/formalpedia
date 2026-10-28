-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans082
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans082
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:04:22.246359+00:00
-- url     : https://prove2.me/theorems/da9dd6fc-b6bd-4e5f-ae8e-1cbf5dd3a24e
-- title:
--   Endpoint22 Reach Plans082 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans082 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan7941`, `ThreeBoundEndpoint22Reachable.plan7942`, `ThreeBoundEndpoint22Reachable.plan7943`, `ThreeBoundEndpoint22Reachable.plan7944`, `ThreeBoundEndpoint22Reachable.plan7945`, `ThreeBoundEndpoint22Reachable.plan7946`, `ThreeBoundEndpoint22Reachable.plan7878`, `ThreeBoundEndpoint22Reachable.plan7947`, `ThreeBoundEndpoint22Reachable.plan7948`, `ThreeBoundEndpoint22Reachable.plan7949`, `ThreeBoundEndpoint22Reachable.plan7950`, `ThreeBoundEndpoint22Reachable.plan7951`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans082.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans062
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
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
def plan7873 : Plan := .step choices225 bits1689 plan6073

def plan7874 : Plan := .step choices225 bits1688 plan6074

def plan7875 : Plan := .step choices225 bits1690 plan6075

def plan7876 : Plan := .step choices225 bits1689 plan6076

def plan7877 : Plan := .step choices225 bits1688 plan6077

def plan7878 : Plan := .step choices225 bits1691 plan6078

def plan7879 : Plan := .step choices225 bits1690 plan6079

def plan7880 : Plan := .step choices225 bits1689 plan6080

def plan7881 : Plan := .step choices225 bits1688 plan6081

def plan7882 : Plan := .step choices225 bits1692 plan6082

def plan7883 : Plan := .step choices225 bits1687 plan6083

def plan7884 : Plan := .step choices225 bits1688 plan6084

def plan7885 : Plan := .step choices225 bits1687 plan6085

def plan7886 : Plan := .step choices225 bits1689 plan6086

def plan7887 : Plan := .step choices225 bits1688 plan6087

def plan7888 : Plan := .step choices225 bits1687 plan6088

def plan7889 : Plan := .step choices225 bits1690 plan6089

def plan7890 : Plan := .step choices225 bits1687 plan6090

def plan7891 : Plan := .step choices225 bits1688 plan6091

def plan7892 : Plan := .step choices225 bits1687 plan6092

def plan7893 : Plan := .step choices225 bits1689 plan6093

def plan7894 : Plan := .step choices225 bits1688 plan6094

def plan7895 : Plan := .step choices225 bits1687 plan6095

def plan7896 : Plan := .step choices225 bits1691 plan6096

def plan7897 : Plan := .step choices225 bits1690 plan6097

def plan7898 : Plan := .step choices225 bits1689 plan6098

def plan7899 : Plan := .step choices225 bits1688 plan6099

def plan7900 : Plan := .step choices225 bits1693 plan6100

def plan7901 : Plan := .step choices225 bits1692 plan6101

def plan7902 : Plan := .step choices225 bits1691 plan6102

def plan7903 : Plan := .step choices225 bits1690 plan6103

def plan7904 : Plan := .step choices225 bits1689 plan6104

def plan7905 : Plan := .step choices226 bits1690 plan6039

def plan7906 : Plan := .step choices226 bits1691 plan6040

def plan7907 : Plan := .step choices226 bits1690 plan6041

def plan7908 : Plan := .step choices226 bits1692 plan6042

def plan7909 : Plan := .step choices226 bits1691 plan6043

def plan7910 : Plan := .step choices226 bits1690 plan6044

def plan7911 : Plan := .step choices226 bits1693 plan6045

def plan7912 : Plan := .step choices226 bits1692 plan6046

def plan7913 : Plan := .step choices226 bits1691 plan6047

def plan7914 : Plan := .step choices226 bits1690 plan6048

def plan7915 : Plan := .step choices226 bits1694 plan6049

def plan7916 : Plan := .step choices226 bits1693 plan6050

def plan7917 : Plan := .step choices226 bits1692 plan6051

def plan7918 : Plan := .step choices226 bits1691 plan6052

def plan7919 : Plan := .step choices226 bits1690 plan6053

def plan7920 : Plan := .step choices226 bits1695 plan6054

def plan7921 : Plan := .step choices226 bits1694 plan6100

def plan7922 : Plan := .step choices226 bits1693 plan6101

def plan7923 : Plan := .step choices226 bits1692 plan6102

def plan7924 : Plan := .step choices226 bits1691 plan6103

def plan7925 : Plan := .step choices226 bits1690 plan6104

def plan7926 : Plan := .step choices227 bits1696 plan6054

def plan7927 : Plan := .step choices228 bits1687 plan5996

def plan7928 : Plan := .step choices228 bits1687 plan5999

def plan7929 : Plan := .step choices228 bits1688 plan6001

def plan7930 : Plan := .step choices228 bits1687 plan6002

def plan7931 : Plan := .step choices228 bits1689 plan6004

def plan7932 : Plan := .step choices228 bits1687 plan6006

def plan7933 : Plan := .step choices228 bits1688 plan6008

def plan7934 : Plan := .step choices228 bits1687 plan6009

def plan7935 : Plan := .step choices228 bits1687 plan6011

def plan7936 : Plan := .step choices228 bits1688 plan6012

def plan7937 : Plan := .step choices228 bits1687 plan6013

def plan7938 : Plan := .step choices228 bits1689 plan6014

def plan7939 : Plan := .step choices228 bits1688 plan6015

def plan7940 : Plan := .step choices228 bits1687 plan6016

def plan7941 : Plan := .step choices228 bits1690 plan6017

def plan7942 : Plan := .step choices228 bits1689 plan6018

def plan7943 : Plan := .step choices228 bits1688 plan6019

def plan7944 : Plan := .step choices228 bits1687 plan6020

def plan7945 : Plan := .step choices228 bits1691 plan6021

def plan7946 : Plan := .step choices228 bits1687 plan6023

def plan7947 : Plan := .step choices228 bits1688 plan6025

def plan7948 : Plan := .step choices228 bits1687 plan6026

def plan7949 : Plan := .step choices228 bits1689 plan6028

def plan7950 : Plan := .step choices228 bits1687 plan6030

def plan7951 : Plan := .step choices228 bits1688 plan6032

def plan7952 : Plan := .step choices228 bits1687 plan6033

def plan7953 : Plan := .step choices228 bits1690 plan6035

def plan7954 : Plan := .step choices228 bits1689 plan6036

def plan7955 : Plan := .step choices228 bits1688 plan6037

def plan7956 : Plan := .step choices228 bits1687 plan6038

def plan7957 : Plan := .step choices228 bits1688 plan6039

def plan7958 : Plan := .step choices228 bits1689 plan6040

def plan7959 : Plan := .step choices228 bits1688 plan6041

def plan7960 : Plan := .step choices228 bits1690 plan6042

def plan7961 : Plan := .step choices228 bits1689 plan6043

def plan7962 : Plan := .step choices228 bits1688 plan6044

def plan7963 : Plan := .step choices228 bits1691 plan6045

def plan7964 : Plan := .step choices228 bits1690 plan6046

def plan7965 : Plan := .step choices228 bits1689 plan6047

def plan7966 : Plan := .step choices228 bits1688 plan6048

def plan7967 : Plan := .step choices228 bits1692 plan6049

def plan7968 : Plan := .step choices228 bits1691 plan6050

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


