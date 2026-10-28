-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans011
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans011
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:45:39.346462+00:00
-- url     : https://prove2.me/theorems/8f8e4cfb-727e-49fa-85a4-fe0430048b92
-- title:
--   Endpoint22 Reach Plans011 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans011 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1127`, `ThreeBoundEndpoint22Reachable.plan1128`, `ThreeBoundEndpoint22Reachable.plan1129`, `ThreeBoundEndpoint22Reachable.plan1130`, `ThreeBoundEndpoint22Reachable.plan1062`, `ThreeBoundEndpoint22Reachable.plan1131`, `ThreeBoundEndpoint22Reachable.plan1132`, `ThreeBoundEndpoint22Reachable.plan1133`, `ThreeBoundEndpoint22Reachable.plan1134`, `ThreeBoundEndpoint22Reachable.plan1135`, `ThreeBoundEndpoint22Reachable.plan1136`, `ThreeBoundEndpoint22Reachable.plan1137`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans011.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
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
def plan1057 : Plan := .step choices94 bits397 plan419

def plan1058 : Plan := .step choices94 bits398 plan420

def plan1059 : Plan := .step choices94 bits399 plan421

def plan1060 : Plan := .step choices94 bits399 plan422

def plan1061 : Plan := .step choices95 bits405 plan408

def plan1062 : Plan := .step choices95 bits405 plan409

def plan1063 : Plan := .step choices95 bits405 plan410

def plan1064 : Plan := .step choices95 bits405 plan411

def plan1065 : Plan := .step choices95 bits405 plan421

def plan1066 : Plan := .step choices95 bits405 plan422

def plan1067 : Plan := .step choices96 bits395 plan390

def plan1068 : Plan := .step choices96 bits396 plan391

def plan1069 : Plan := .step choices96 bits396 plan392

def plan1070 : Plan := .step choices96 bits395 plan393

def plan1071 : Plan := .step choices96 bits396 plan394

def plan1072 : Plan := .step choices96 bits402 plan395

def plan1073 : Plan := .step choices96 bits402 plan396

def plan1074 : Plan := .step choices96 bits402 plan397

def plan1075 : Plan := .step choices96 bits400 plan398

def plan1076 : Plan := .step choices96 bits313 plan399

def plan1077 : Plan := .step choices96 bits313 plan400

def plan1078 : Plan := .step choices96 bits313 plan401

def plan1079 : Plan := .step choices96 bits401 plan402

def plan1080 : Plan := .step choices96 bits314 plan403

def plan1081 : Plan := .step choices96 bits315 plan404

def plan1082 : Plan := .step choices96 bits315 plan405

def plan1083 : Plan := .step choices96 bits314 plan406

def plan1084 : Plan := .step choices96 bits315 plan407

def plan1085 : Plan := .step choices96 bits317 plan408

def plan1086 : Plan := .step choices96 bits317 plan409

def plan1087 : Plan := .step choices96 bits317 plan410

def plan1088 : Plan := .step choices96 bits317 plan411

def plan1089 : Plan := .step choices96 bits400 plan412

def plan1090 : Plan := .step choices96 bits313 plan413

def plan1091 : Plan := .step choices96 bits313 plan414

def plan1092 : Plan := .step choices96 bits313 plan415

def plan1093 : Plan := .step choices96 bits401 plan416

def plan1094 : Plan := .step choices96 bits315 plan417

def plan1095 : Plan := .step choices96 bits315 plan418

def plan1096 : Plan := .step choices96 bits314 plan419

def plan1097 : Plan := .step choices96 bits315 plan420

def plan1098 : Plan := .step choices96 bits317 plan421

def plan1099 : Plan := .step choices96 bits317 plan422

def plan1100 : Plan := .step choices97 bits404 plan395

def plan1101 : Plan := .step choices97 bits404 plan396

def plan1102 : Plan := .step choices97 bits404 plan397

def plan1103 : Plan := .step choices97 bits403 plan402

def plan1104 : Plan := .step choices97 bits316 plan403

def plan1105 : Plan := .step choices97 bits318 plan404

def plan1106 : Plan := .step choices97 bits318 plan405

def plan1107 : Plan := .step choices97 bits316 plan406

def plan1108 : Plan := .step choices97 bits318 plan407

def plan1109 : Plan := .step choices97 bits319 plan408

def plan1110 : Plan := .step choices97 bits319 plan409

def plan1111 : Plan := .step choices97 bits319 plan410

def plan1112 : Plan := .step choices97 bits319 plan411

def plan1113 : Plan := .step choices97 bits403 plan416

def plan1114 : Plan := .step choices97 bits318 plan417

def plan1115 : Plan := .step choices97 bits318 plan418

def plan1116 : Plan := .step choices97 bits316 plan419

def plan1117 : Plan := .step choices97 bits318 plan420

def plan1118 : Plan := .step choices97 bits319 plan421

def plan1119 : Plan := .step choices97 bits319 plan422

def plan1120 : Plan := .step choices98 bits320 plan408

def plan1121 : Plan := .step choices98 bits320 plan409

def plan1122 : Plan := .step choices98 bits320 plan410

def plan1123 : Plan := .step choices98 bits320 plan411

def plan1124 : Plan := .step choices98 bits320 plan421

def plan1125 : Plan := .step choices98 bits320 plan422

def plan1126 : Plan := .step choices99 bits320 plan411

def plan1127 : Plan := .step choices100 bits395 plan390

def plan1128 : Plan := .step choices100 bits396 plan391

def plan1129 : Plan := .step choices100 bits396 plan392

def plan1130 : Plan := .step choices100 bits395 plan393

def plan1131 : Plan := .step choices100 bits396 plan394

def plan1132 : Plan := .step choices100 bits402 plan395

def plan1133 : Plan := .step choices100 bits402 plan396

def plan1134 : Plan := .step choices100 bits402 plan397

def plan1135 : Plan := .step choices100 bits401 plan402

def plan1136 : Plan := .step choices100 bits314 plan403

def plan1137 : Plan := .step choices100 bits315 plan404

def plan1138 : Plan := .step choices100 bits315 plan405

def plan1139 : Plan := .step choices100 bits314 plan406

def plan1140 : Plan := .step choices100 bits315 plan407

def plan1141 : Plan := .step choices100 bits317 plan408

def plan1142 : Plan := .step choices100 bits317 plan409

def plan1143 : Plan := .step choices100 bits317 plan410

def plan1144 : Plan := .step choices100 bits317 plan411

def plan1145 : Plan := .step choices100 bits400 plan412

def plan1146 : Plan := .step choices100 bits313 plan413

def plan1147 : Plan := .step choices100 bits313 plan414

def plan1148 : Plan := .step choices100 bits313 plan415

def plan1149 : Plan := .step choices100 bits401 plan416

def plan1150 : Plan := .step choices100 bits315 plan417

def plan1151 : Plan := .step choices100 bits315 plan418

def plan1152 : Plan := .step choices100 bits314 plan419

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


