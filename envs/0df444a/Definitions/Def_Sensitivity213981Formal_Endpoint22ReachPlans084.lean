-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans084
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans084
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:03:58.172074+00:00
-- url     : https://prove2.me/theorems/d9607d3d-912c-42f6-bcf4-aaf5b55dd258
-- title:
--   Endpoint22 Reach Plans084 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans084 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8132`, `ThreeBoundEndpoint22Reachable.plan8133`, `ThreeBoundEndpoint22Reachable.plan8134`, `ThreeBoundEndpoint22Reachable.plan8135`, `ThreeBoundEndpoint22Reachable.plan8136`, `ThreeBoundEndpoint22Reachable.plan8137`, `ThreeBoundEndpoint22Reachable.plan8069`, `ThreeBoundEndpoint22Reachable.plan8138`, `ThreeBoundEndpoint22Reachable.plan8139`, `ThreeBoundEndpoint22Reachable.plan8140`, `ThreeBoundEndpoint22Reachable.plan8141`, `ThreeBoundEndpoint22Reachable.plan8142`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans084.lean, lines 1–209.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
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
def plan8065 : Plan := .step choices229 bits1689 plan6104

def plan8066 : Plan := .step choices230 bits1695 plan6054

def plan8067 : Plan := .step choices230 bits1694 plan6100

def plan8068 : Plan := .step choices230 bits1693 plan6101

def plan8069 : Plan := .step choices230 bits1692 plan6102

def plan8070 : Plan := .step choices230 bits1691 plan6103

def plan8071 : Plan := .step choices230 bits1690 plan6104

def plan8072 : Plan := .step choices231 bits621 plan6105

def plan8073 : Plan := .step choices233 bits916 plan6106

def plan8074 : Plan := .step choices233 bits917 plan6107

def plan8075 : Plan := .step choices233 bits916 plan6108

def plan8076 : Plan := .step choices238 bits1155 plan6113

def plan8077 : Plan := .step choices239 bits1163 plan6109

def plan8078 : Plan := .step choices239 bits1159 plan6110

def plan8079 : Plan := .step choices239 bits1160 plan6111

def plan8080 : Plan := .step choices239 bits1159 plan6112

def plan8081 : Plan := .step choices239 bits1161 plan6113

def plan8082 : Plan := .step choices239 bits1160 plan6114

def plan8083 : Plan := .step choices239 bits1159 plan6115

def plan8084 : Plan := .step choices247 bits1380 plan6116

def plan8085 : Plan := .step choices247 bits1381 plan6123

def plan8086 : Plan := .step choices247 bits1382 plan6126

def plan8087 : Plan := .step choices247 bits1381 plan6127

def plan8088 : Plan := .step choices248 bits1394 plan6117

def plan8089 : Plan := .step choices248 bits1395 plan6118

def plan8090 : Plan := .step choices248 bits1394 plan6119

def plan8091 : Plan := .step choices248 bits1383 plan6120

def plan8092 : Plan := .step choices248 bits1384 plan6121

def plan8093 : Plan := .step choices248 bits1383 plan6122

def plan8094 : Plan := .step choices248 bits1385 plan6123

def plan8095 : Plan := .step choices248 bits1384 plan6124

def plan8096 : Plan := .step choices248 bits1383 plan6125

def plan8097 : Plan := .step choices248 bits1386 plan6126

def plan8098 : Plan := .step choices248 bits1385 plan6127

def plan8099 : Plan := .step choices248 bits1384 plan6128

def plan8100 : Plan := .step choices248 bits1383 plan6129

def plan8101 : Plan := .step choices250 bits1384 plan6118

def plan8102 : Plan := .step choices254 bits1384 plan6118

def plan8103 : Plan := .step choices257 bits1541 plan6150

def plan8104 : Plan := .step choices258 bits1543 plan6130

def plan8105 : Plan := .step choices258 bits1544 plan6131

def plan8106 : Plan := .step choices258 bits1543 plan6132

def plan8107 : Plan := .step choices258 bits1557 plan6137

def plan8108 : Plan := .step choices258 bits1546 plan6143

def plan8109 : Plan := .step choices258 bits1548 plan6146

def plan8110 : Plan := .step choices258 bits1546 plan6147

def plan8111 : Plan := .step choices258 bits1549 plan6150

def plan8112 : Plan := .step choices258 bits1548 plan6151

def plan8113 : Plan := .step choices258 bits1546 plan6152

def plan8114 : Plan := .step choices258 bits1542 plan6155

def plan8115 : Plan := .step choices258 bits1542 plan6156

def plan8116 : Plan := .step choices259 bits1558 plan6134

def plan8117 : Plan := .step choices259 bits1559 plan6135

def plan8118 : Plan := .step choices259 bits1558 plan6136

def plan8119 : Plan := .step choices259 bits1560 plan6137

def plan8120 : Plan := .step choices259 bits1559 plan6138

def plan8121 : Plan := .step choices259 bits1558 plan6139

def plan8122 : Plan := .step choices259 bits1550 plan6140

def plan8123 : Plan := .step choices259 bits1551 plan6141

def plan8124 : Plan := .step choices259 bits1550 plan6142

def plan8125 : Plan := .step choices259 bits1552 plan6143

def plan8126 : Plan := .step choices259 bits1551 plan6144

def plan8127 : Plan := .step choices259 bits1550 plan6145

def plan8128 : Plan := .step choices259 bits1553 plan6146

def plan8129 : Plan := .step choices259 bits1552 plan6147

def plan8130 : Plan := .step choices259 bits1551 plan6148

def plan8131 : Plan := .step choices259 bits1550 plan6149

def plan8132 : Plan := .step choices259 bits1554 plan6150

def plan8133 : Plan := .step choices259 bits1553 plan6151

def plan8134 : Plan := .step choices259 bits1552 plan6152

def plan8135 : Plan := .step choices259 bits1551 plan6153

def plan8136 : Plan := .step choices259 bits1550 plan6154

def plan8137 : Plan := .step choices261 bits1556 plan6133

def plan8138 : Plan := .step choices261 bits1545 plan6135

def plan8139 : Plan := .step choices261 bits1547 plan6137

def plan8140 : Plan := .step choices261 bits1545 plan6138

def plan8141 : Plan := .step choices265 bits1556 plan6133

def plan8142 : Plan := .step choices265 bits1545 plan6135

def plan8143 : Plan := .step choices265 bits1547 plan6137

def plan8144 : Plan := .step choices265 bits1545 plan6138

def plan8145 : Plan := .step choices268 bits1623 plan6185

def plan8146 : Plan := .step choices268 bits1624 plan6190

def plan8147 : Plan := .step choices268 bits1623 plan6195

def plan8148 : Plan := .step choices269 bits1638 plan6157

def plan8149 : Plan := .step choices269 bits1639 plan6164

def plan8150 : Plan := .step choices269 bits1640 plan6167

def plan8151 : Plan := .step choices269 bits1639 plan6168

def plan8152 : Plan := .step choices269 bits1625 plan6172

def plan8153 : Plan := .step choices269 bits1627 plan6173

def plan8154 : Plan := .step choices269 bits1625 plan6174

def plan8155 : Plan := .step choices269 bits1625 plan6178

def plan8156 : Plan := .step choices269 bits1627 plan6181

def plan8157 : Plan := .step choices269 bits1625 plan6182

def plan8158 : Plan := .step choices269 bits1628 plan6185

def plan8159 : Plan := .step choices269 bits1627 plan6186

def plan8160 : Plan := .step choices269 bits1625 plan6187

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


