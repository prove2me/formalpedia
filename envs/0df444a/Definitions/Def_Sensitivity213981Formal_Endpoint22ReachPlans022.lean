-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans022
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans022
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:02.908792+00:00
-- url     : https://prove2.me/theorems/4de6b754-4c64-4a1c-9cdd-ed3ab577b817
-- title:
--   Endpoint22 Reach Plans022 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans022 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2182`, `ThreeBoundEndpoint22Reachable.plan2183`, `ThreeBoundEndpoint22Reachable.plan2184`, `ThreeBoundEndpoint22Reachable.plan2185`, `ThreeBoundEndpoint22Reachable.plan2186`, `ThreeBoundEndpoint22Reachable.plan2187`, `ThreeBoundEndpoint22Reachable.plan2188`, `ThreeBoundEndpoint22Reachable.plan2118`, `ThreeBoundEndpoint22Reachable.plan2189`, `ThreeBoundEndpoint22Reachable.plan2190`, `ThreeBoundEndpoint22Reachable.plan2191`, `ThreeBoundEndpoint22Reachable.plan2192`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans022.lean, lines 1–205.

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
def plan2113 : Plan := .step choices93 bits653 plan1118

def plan2114 : Plan := .step choices93 bits653 plan1119

def plan2115 : Plan := .step choices93 bits654 plan1120

def plan2116 : Plan := .step choices93 bits654 plan1121

def plan2117 : Plan := .step choices93 bits654 plan1122

def plan2118 : Plan := .step choices93 bits654 plan1123

def plan2119 : Plan := .step choices93 bits654 plan1124

def plan2120 : Plan := .step choices93 bits654 plan1125

def plan2121 : Plan := .step choices93 bits654 plan1126

def plan2122 : Plan := .step choices93 bits648 plan1136

def plan2123 : Plan := .step choices93 bits649 plan1137

def plan2124 : Plan := .step choices93 bits649 plan1138

def plan2125 : Plan := .step choices93 bits648 plan1139

def plan2126 : Plan := .step choices93 bits649 plan1140

def plan2127 : Plan := .step choices93 bits651 plan1141

def plan2128 : Plan := .step choices93 bits651 plan1142

def plan2129 : Plan := .step choices93 bits651 plan1143

def plan2130 : Plan := .step choices93 bits651 plan1144

def plan2131 : Plan := .step choices93 bits647 plan1146

def plan2132 : Plan := .step choices93 bits647 plan1147

def plan2133 : Plan := .step choices93 bits647 plan1148

def plan2134 : Plan := .step choices93 bits649 plan1150

def plan2135 : Plan := .step choices93 bits649 plan1151

def plan2136 : Plan := .step choices93 bits648 plan1152

def plan2137 : Plan := .step choices93 bits649 plan1153

def plan2138 : Plan := .step choices93 bits651 plan1154

def plan2139 : Plan := .step choices93 bits651 plan1155

def plan2140 : Plan := .step choices93 bits653 plan1159

def plan2141 : Plan := .step choices93 bits653 plan1160

def plan2142 : Plan := .step choices93 bits653 plan1161

def plan2143 : Plan := .step choices93 bits653 plan1162

def plan2144 : Plan := .step choices93 bits652 plan1164

def plan2145 : Plan := .step choices93 bits652 plan1165

def plan2146 : Plan := .step choices93 bits650 plan1166

def plan2147 : Plan := .step choices93 bits652 plan1167

def plan2148 : Plan := .step choices93 bits653 plan1168

def plan2149 : Plan := .step choices93 bits653 plan1169

def plan2150 : Plan := .step choices93 bits654 plan1170

def plan2151 : Plan := .step choices93 bits654 plan1171

def plan2152 : Plan := .step choices93 bits654 plan1172

def plan2153 : Plan := .step choices94 bits660 plan1104

def plan2154 : Plan := .step choices94 bits661 plan1105

def plan2155 : Plan := .step choices94 bits661 plan1106

def plan2156 : Plan := .step choices94 bits660 plan1107

def plan2157 : Plan := .step choices94 bits661 plan1108

def plan2158 : Plan := .step choices94 bits662 plan1109

def plan2159 : Plan := .step choices94 bits662 plan1110

def plan2160 : Plan := .step choices94 bits662 plan1111

def plan2161 : Plan := .step choices94 bits662 plan1112

def plan2162 : Plan := .step choices94 bits661 plan1114

def plan2163 : Plan := .step choices94 bits661 plan1115

def plan2164 : Plan := .step choices94 bits660 plan1116

def plan2165 : Plan := .step choices94 bits661 plan1117

def plan2166 : Plan := .step choices94 bits662 plan1118

def plan2167 : Plan := .step choices94 bits662 plan1119

def plan2168 : Plan := .step choices94 bits663 plan1120

def plan2169 : Plan := .step choices94 bits663 plan1121

def plan2170 : Plan := .step choices94 bits663 plan1122

def plan2171 : Plan := .step choices94 bits663 plan1123

def plan2172 : Plan := .step choices94 bits663 plan1124

def plan2173 : Plan := .step choices94 bits663 plan1125

def plan2174 : Plan := .step choices94 bits663 plan1126

def plan2175 : Plan := .step choices94 bits662 plan1159

def plan2176 : Plan := .step choices94 bits662 plan1160

def plan2177 : Plan := .step choices94 bits662 plan1161

def plan2178 : Plan := .step choices94 bits662 plan1162

def plan2179 : Plan := .step choices94 bits661 plan1164

def plan2180 : Plan := .step choices94 bits661 plan1165

def plan2181 : Plan := .step choices94 bits660 plan1166

def plan2182 : Plan := .step choices94 bits661 plan1167

def plan2183 : Plan := .step choices94 bits662 plan1168

def plan2184 : Plan := .step choices94 bits662 plan1169

def plan2185 : Plan := .step choices94 bits663 plan1170

def plan2186 : Plan := .step choices94 bits663 plan1171

def plan2187 : Plan := .step choices94 bits663 plan1172

def plan2188 : Plan := .step choices95 bits673 plan1120

def plan2189 : Plan := .step choices95 bits673 plan1121

def plan2190 : Plan := .step choices95 bits673 plan1122

def plan2191 : Plan := .step choices95 bits673 plan1123

def plan2192 : Plan := .step choices95 bits673 plan1124

def plan2193 : Plan := .step choices95 bits673 plan1125

def plan2194 : Plan := .step choices95 bits673 plan1126

def plan2195 : Plan := .step choices95 bits673 plan1170

def plan2196 : Plan := .step choices95 bits673 plan1171

def plan2197 : Plan := .step choices95 bits673 plan1172

def plan2198 : Plan := .step choices96 bits657 plan1046

def plan2199 : Plan := .step choices96 bits658 plan1047

def plan2200 : Plan := .step choices96 bits658 plan1048

def plan2201 : Plan := .step choices96 bits657 plan1049

def plan2202 : Plan := .step choices96 bits658 plan1050

def plan2203 : Plan := .step choices96 bits659 plan1051

def plan2204 : Plan := .step choices96 bits659 plan1052

def plan2205 : Plan := .step choices96 bits659 plan1053

def plan2206 : Plan := .step choices96 bits659 plan1054

def plan2207 : Plan := .step choices96 bits658 plan1055

def plan2208 : Plan := .step choices96 bits658 plan1056

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


