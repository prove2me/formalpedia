-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans021
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans021
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:18.735288+00:00
-- url     : https://prove2.me/theorems/9d0a3524-13e3-4d54-a4e6-b5ff2484d266
-- title:
--   Endpoint22 Reach Plans021 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans021 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2085`, `ThreeBoundEndpoint22Reachable.plan2086`, `ThreeBoundEndpoint22Reachable.plan2087`, `ThreeBoundEndpoint22Reachable.plan2088`, `ThreeBoundEndpoint22Reachable.plan2089`, `ThreeBoundEndpoint22Reachable.plan2090`, `ThreeBoundEndpoint22Reachable.plan2091`, `ThreeBoundEndpoint22Reachable.plan2092`, `ThreeBoundEndpoint22Reachable.plan2093`, `ThreeBoundEndpoint22Reachable.plan2022`, `ThreeBoundEndpoint22Reachable.plan2094`, `ThreeBoundEndpoint22Reachable.plan2095`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans021.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans011
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
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
def plan2017 : Plan := .step choices90 bits506 plan998

def plan2018 : Plan := .step choices90 bits506 plan999

def plan2019 : Plan := .step choices90 bits505 plan1041

def plan2020 : Plan := .step choices92 bits641 plan1081

def plan2021 : Plan := .step choices92 bits641 plan1082

def plan2022 : Plan := .step choices92 bits641 plan1084

def plan2023 : Plan := .step choices92 bits643 plan1085

def plan2024 : Plan := .step choices92 bits643 plan1086

def plan2025 : Plan := .step choices92 bits643 plan1087

def plan2026 : Plan := .step choices92 bits643 plan1088

def plan2027 : Plan := .step choices92 bits641 plan1094

def plan2028 : Plan := .step choices92 bits641 plan1095

def plan2029 : Plan := .step choices92 bits641 plan1097

def plan2030 : Plan := .step choices92 bits643 plan1098

def plan2031 : Plan := .step choices92 bits643 plan1099

def plan2032 : Plan := .step choices92 bits642 plan1104

def plan2033 : Plan := .step choices92 bits644 plan1105

def plan2034 : Plan := .step choices92 bits644 plan1106

def plan2035 : Plan := .step choices92 bits642 plan1107

def plan2036 : Plan := .step choices92 bits644 plan1108

def plan2037 : Plan := .step choices92 bits645 plan1109

def plan2038 : Plan := .step choices92 bits645 plan1110

def plan2039 : Plan := .step choices92 bits645 plan1111

def plan2040 : Plan := .step choices92 bits645 plan1112

def plan2041 : Plan := .step choices92 bits644 plan1114

def plan2042 : Plan := .step choices92 bits644 plan1115

def plan2043 : Plan := .step choices92 bits642 plan1116

def plan2044 : Plan := .step choices92 bits644 plan1117

def plan2045 : Plan := .step choices92 bits645 plan1118

def plan2046 : Plan := .step choices92 bits645 plan1119

def plan2047 : Plan := .step choices92 bits646 plan1120

def plan2048 : Plan := .step choices92 bits646 plan1121

def plan2049 : Plan := .step choices92 bits646 plan1122

def plan2050 : Plan := .step choices92 bits646 plan1123

def plan2051 : Plan := .step choices92 bits646 plan1124

def plan2052 : Plan := .step choices92 bits646 plan1125

def plan2053 : Plan := .step choices92 bits646 plan1126

def plan2054 : Plan := .step choices92 bits641 plan1137

def plan2055 : Plan := .step choices92 bits641 plan1138

def plan2056 : Plan := .step choices92 bits641 plan1140

def plan2057 : Plan := .step choices92 bits643 plan1141

def plan2058 : Plan := .step choices92 bits643 plan1142

def plan2059 : Plan := .step choices92 bits643 plan1143

def plan2060 : Plan := .step choices92 bits643 plan1144

def plan2061 : Plan := .step choices92 bits641 plan1150

def plan2062 : Plan := .step choices92 bits641 plan1151

def plan2063 : Plan := .step choices92 bits641 plan1153

def plan2064 : Plan := .step choices92 bits643 plan1154

def plan2065 : Plan := .step choices92 bits643 plan1155

def plan2066 : Plan := .step choices92 bits645 plan1159

def plan2067 : Plan := .step choices92 bits645 plan1160

def plan2068 : Plan := .step choices92 bits645 plan1161

def plan2069 : Plan := .step choices92 bits645 plan1162

def plan2070 : Plan := .step choices92 bits644 plan1164

def plan2071 : Plan := .step choices92 bits644 plan1165

def plan2072 : Plan := .step choices92 bits642 plan1166

def plan2073 : Plan := .step choices92 bits644 plan1167

def plan2074 : Plan := .step choices92 bits645 plan1168

def plan2075 : Plan := .step choices92 bits645 plan1169

def plan2076 : Plan := .step choices92 bits646 plan1170

def plan2077 : Plan := .step choices92 bits646 plan1171

def plan2078 : Plan := .step choices92 bits646 plan1172

def plan2079 : Plan := .step choices93 bits647 plan1076

def plan2080 : Plan := .step choices93 bits647 plan1077

def plan2081 : Plan := .step choices93 bits647 plan1078

def plan2082 : Plan := .step choices93 bits648 plan1080

def plan2083 : Plan := .step choices93 bits649 plan1081

def plan2084 : Plan := .step choices93 bits649 plan1082

def plan2085 : Plan := .step choices93 bits648 plan1083

def plan2086 : Plan := .step choices93 bits649 plan1084

def plan2087 : Plan := .step choices93 bits651 plan1085

def plan2088 : Plan := .step choices93 bits651 plan1086

def plan2089 : Plan := .step choices93 bits651 plan1087

def plan2090 : Plan := .step choices93 bits651 plan1088

def plan2091 : Plan := .step choices93 bits647 plan1090

def plan2092 : Plan := .step choices93 bits647 plan1091

def plan2093 : Plan := .step choices93 bits647 plan1092

def plan2094 : Plan := .step choices93 bits649 plan1094

def plan2095 : Plan := .step choices93 bits649 plan1095

def plan2096 : Plan := .step choices93 bits648 plan1096

def plan2097 : Plan := .step choices93 bits649 plan1097

def plan2098 : Plan := .step choices93 bits651 plan1098

def plan2099 : Plan := .step choices93 bits651 plan1099

def plan2100 : Plan := .step choices93 bits650 plan1104

def plan2101 : Plan := .step choices93 bits652 plan1105

def plan2102 : Plan := .step choices93 bits652 plan1106

def plan2103 : Plan := .step choices93 bits650 plan1107

def plan2104 : Plan := .step choices93 bits652 plan1108

def plan2105 : Plan := .step choices93 bits653 plan1109

def plan2106 : Plan := .step choices93 bits653 plan1110

def plan2107 : Plan := .step choices93 bits653 plan1111

def plan2108 : Plan := .step choices93 bits653 plan1112

def plan2109 : Plan := .step choices93 bits652 plan1114

def plan2110 : Plan := .step choices93 bits652 plan1115

def plan2111 : Plan := .step choices93 bits650 plan1116

def plan2112 : Plan := .step choices93 bits652 plan1117

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


