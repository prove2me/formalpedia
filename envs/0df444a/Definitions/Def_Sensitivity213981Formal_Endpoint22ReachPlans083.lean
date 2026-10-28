-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans083
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans083
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:04:06.116775+00:00
-- url     : https://prove2.me/theorems/a6639f94-0940-4e55-a8d9-744f6694318b
-- title:
--   Endpoint22 Reach Plans083 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans083 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8037`, `ThreeBoundEndpoint22Reachable.plan8038`, `ThreeBoundEndpoint22Reachable.plan8039`, `ThreeBoundEndpoint22Reachable.plan8040`, `ThreeBoundEndpoint22Reachable.plan8041`, `ThreeBoundEndpoint22Reachable.plan8042`, `ThreeBoundEndpoint22Reachable.plan7974`, `ThreeBoundEndpoint22Reachable.plan8043`, `ThreeBoundEndpoint22Reachable.plan8044`, `ThreeBoundEndpoint22Reachable.plan8045`, `ThreeBoundEndpoint22Reachable.plan8046`, `ThreeBoundEndpoint22Reachable.plan8047`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans083.lean, lines 1–204.

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
def plan7969 : Plan := .step choices228 bits1690 plan6051

def plan7970 : Plan := .step choices228 bits1689 plan6052

def plan7971 : Plan := .step choices228 bits1688 plan6053

def plan7972 : Plan := .step choices228 bits1693 plan6054

def plan7973 : Plan := .step choices228 bits1687 plan6055

def plan7974 : Plan := .step choices228 bits1688 plan6056

def plan7975 : Plan := .step choices228 bits1687 plan6057

def plan7976 : Plan := .step choices228 bits1687 plan6058

def plan7977 : Plan := .step choices228 bits1688 plan6059

def plan7978 : Plan := .step choices228 bits1687 plan6060

def plan7979 : Plan := .step choices228 bits1689 plan6061

def plan7980 : Plan := .step choices228 bits1688 plan6062

def plan7981 : Plan := .step choices228 bits1687 plan6063

def plan7982 : Plan := .step choices228 bits1690 plan6064

def plan7983 : Plan := .step choices228 bits1687 plan6065

def plan7984 : Plan := .step choices228 bits1687 plan6066

def plan7985 : Plan := .step choices228 bits1688 plan6067

def plan7986 : Plan := .step choices228 bits1687 plan6068

def plan7987 : Plan := .step choices228 bits1689 plan6069

def plan7988 : Plan := .step choices228 bits1688 plan6070

def plan7989 : Plan := .step choices228 bits1687 plan6071

def plan7990 : Plan := .step choices228 bits1687 plan6072

def plan7991 : Plan := .step choices228 bits1688 plan6073

def plan7992 : Plan := .step choices228 bits1687 plan6074

def plan7993 : Plan := .step choices228 bits1689 plan6075

def plan7994 : Plan := .step choices228 bits1688 plan6076

def plan7995 : Plan := .step choices228 bits1687 plan6077

def plan7996 : Plan := .step choices228 bits1690 plan6078

def plan7997 : Plan := .step choices228 bits1689 plan6079

def plan7998 : Plan := .step choices228 bits1688 plan6080

def plan7999 : Plan := .step choices228 bits1687 plan6081

def plan8000 : Plan := .step choices228 bits1691 plan6082

def plan8001 : Plan := .step choices228 bits1687 plan6084

def plan8002 : Plan := .step choices228 bits1688 plan6086

def plan8003 : Plan := .step choices228 bits1687 plan6087

def plan8004 : Plan := .step choices228 bits1689 plan6089

def plan8005 : Plan := .step choices228 bits1687 plan6091

def plan8006 : Plan := .step choices228 bits1688 plan6093

def plan8007 : Plan := .step choices228 bits1687 plan6094

def plan8008 : Plan := .step choices228 bits1690 plan6096

def plan8009 : Plan := .step choices228 bits1689 plan6097

def plan8010 : Plan := .step choices228 bits1688 plan6098

def plan8011 : Plan := .step choices228 bits1687 plan6099

def plan8012 : Plan := .step choices228 bits1692 plan6100

def plan8013 : Plan := .step choices228 bits1691 plan6101

def plan8014 : Plan := .step choices228 bits1690 plan6102

def plan8015 : Plan := .step choices228 bits1689 plan6103

def plan8016 : Plan := .step choices228 bits1688 plan6104

def plan8017 : Plan := .step choices229 bits1689 plan6039

def plan8018 : Plan := .step choices229 bits1690 plan6040

def plan8019 : Plan := .step choices229 bits1689 plan6041

def plan8020 : Plan := .step choices229 bits1691 plan6042

def plan8021 : Plan := .step choices229 bits1690 plan6043

def plan8022 : Plan := .step choices229 bits1689 plan6044

def plan8023 : Plan := .step choices229 bits1692 plan6045

def plan8024 : Plan := .step choices229 bits1691 plan6046

def plan8025 : Plan := .step choices229 bits1690 plan6047

def plan8026 : Plan := .step choices229 bits1689 plan6048

def plan8027 : Plan := .step choices229 bits1693 plan6049

def plan8028 : Plan := .step choices229 bits1692 plan6050

def plan8029 : Plan := .step choices229 bits1691 plan6051

def plan8030 : Plan := .step choices229 bits1690 plan6052

def plan8031 : Plan := .step choices229 bits1689 plan6053

def plan8032 : Plan := .step choices229 bits1694 plan6054

def plan8033 : Plan := .step choices229 bits1688 plan6072

def plan8034 : Plan := .step choices229 bits1689 plan6073

def plan8035 : Plan := .step choices229 bits1688 plan6074

def plan8036 : Plan := .step choices229 bits1690 plan6075

def plan8037 : Plan := .step choices229 bits1689 plan6076

def plan8038 : Plan := .step choices229 bits1688 plan6077

def plan8039 : Plan := .step choices229 bits1691 plan6078

def plan8040 : Plan := .step choices229 bits1690 plan6079

def plan8041 : Plan := .step choices229 bits1689 plan6080

def plan8042 : Plan := .step choices229 bits1688 plan6081

def plan8043 : Plan := .step choices229 bits1692 plan6082

def plan8044 : Plan := .step choices229 bits1687 plan6083

def plan8045 : Plan := .step choices229 bits1688 plan6084

def plan8046 : Plan := .step choices229 bits1687 plan6085

def plan8047 : Plan := .step choices229 bits1689 plan6086

def plan8048 : Plan := .step choices229 bits1688 plan6087

def plan8049 : Plan := .step choices229 bits1687 plan6088

def plan8050 : Plan := .step choices229 bits1690 plan6089

def plan8051 : Plan := .step choices229 bits1687 plan6090

def plan8052 : Plan := .step choices229 bits1688 plan6091

def plan8053 : Plan := .step choices229 bits1687 plan6092

def plan8054 : Plan := .step choices229 bits1689 plan6093

def plan8055 : Plan := .step choices229 bits1688 plan6094

def plan8056 : Plan := .step choices229 bits1687 plan6095

def plan8057 : Plan := .step choices229 bits1691 plan6096

def plan8058 : Plan := .step choices229 bits1690 plan6097

def plan8059 : Plan := .step choices229 bits1689 plan6098

def plan8060 : Plan := .step choices229 bits1688 plan6099

def plan8061 : Plan := .step choices229 bits1693 plan6100

def plan8062 : Plan := .step choices229 bits1692 plan6101

def plan8063 : Plan := .step choices229 bits1691 plan6102

def plan8064 : Plan := .step choices229 bits1690 plan6103

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


