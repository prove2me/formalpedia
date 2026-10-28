-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans012
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:45:51.499122+00:00
-- url     : https://prove2.me/theorems/6dda7168-1cb9-4f83-8fca-8581df1a8e5a
-- title:
--   Endpoint22 Reach Plans012 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans012 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1222`, `ThreeBoundEndpoint22Reachable.plan1223`, `ThreeBoundEndpoint22Reachable.plan1224`, `ThreeBoundEndpoint22Reachable.plan1225`, `ThreeBoundEndpoint22Reachable.plan1226`, `ThreeBoundEndpoint22Reachable.plan1227`, `ThreeBoundEndpoint22Reachable.plan1228`, `ThreeBoundEndpoint22Reachable.plan1158`, `ThreeBoundEndpoint22Reachable.plan1229`, `ThreeBoundEndpoint22Reachable.plan1230`, `ThreeBoundEndpoint22Reachable.plan1231`, `ThreeBoundEndpoint22Reachable.plan1232`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans012.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
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
def plan1153 : Plan := .step choices100 bits315 plan420

def plan1154 : Plan := .step choices100 bits317 plan421

def plan1155 : Plan := .step choices100 bits317 plan422

def plan1156 : Plan := .step choices101 bits404 plan395

def plan1157 : Plan := .step choices101 bits404 plan396

def plan1158 : Plan := .step choices101 bits404 plan397

def plan1159 : Plan := .step choices101 bits319 plan408

def plan1160 : Plan := .step choices101 bits319 plan409

def plan1161 : Plan := .step choices101 bits319 plan410

def plan1162 : Plan := .step choices101 bits319 plan411

def plan1163 : Plan := .step choices101 bits403 plan416

def plan1164 : Plan := .step choices101 bits318 plan417

def plan1165 : Plan := .step choices101 bits318 plan418

def plan1166 : Plan := .step choices101 bits316 plan419

def plan1167 : Plan := .step choices101 bits318 plan420

def plan1168 : Plan := .step choices101 bits319 plan421

def plan1169 : Plan := .step choices101 bits319 plan422

def plan1170 : Plan := .step choices102 bits320 plan411

def plan1171 : Plan := .step choices102 bits320 plan421

def plan1172 : Plan := .step choices102 bits320 plan422

def plan1173 : Plan := .step choices103 bits446 plan423

def plan1174 : Plan := .step choices103 bits446 plan424

def plan1175 : Plan := .step choices103 bits446 plan425

def plan1176 : Plan := .step choices103 bits446 plan426

def plan1177 : Plan := .step choices103 bits447 plan427

def plan1178 : Plan := .step choices103 bits447 plan428

def plan1179 : Plan := .step choices103 bits446 plan429

def plan1180 : Plan := .step choices103 bits447 plan430

def plan1181 : Plan := .step choices103 bits448 plan431

def plan1182 : Plan := .step choices103 bits448 plan432

def plan1183 : Plan := .step choices103 bits448 plan433

def plan1184 : Plan := .step choices103 bits448 plan434

def plan1185 : Plan := .step choices103 bits446 plan435

def plan1186 : Plan := .step choices103 bits446 plan436

def plan1187 : Plan := .step choices103 bits446 plan437

def plan1188 : Plan := .step choices103 bits447 plan438

def plan1189 : Plan := .step choices103 bits447 plan439

def plan1190 : Plan := .step choices103 bits446 plan440

def plan1191 : Plan := .step choices103 bits447 plan441

def plan1192 : Plan := .step choices103 bits448 plan442

def plan1193 : Plan := .step choices103 bits448 plan443

def plan1194 : Plan := .step choices104 bits447 plan426

def plan1195 : Plan := .step choices104 bits448 plan427

def plan1196 : Plan := .step choices104 bits448 plan428

def plan1197 : Plan := .step choices104 bits447 plan429

def plan1198 : Plan := .step choices104 bits448 plan430

def plan1199 : Plan := .step choices104 bits449 plan431

def plan1200 : Plan := .step choices104 bits449 plan432

def plan1201 : Plan := .step choices104 bits449 plan433

def plan1202 : Plan := .step choices104 bits449 plan434

def plan1203 : Plan := .step choices104 bits448 plan438

def plan1204 : Plan := .step choices104 bits448 plan439

def plan1205 : Plan := .step choices104 bits447 plan440

def plan1206 : Plan := .step choices104 bits448 plan441

def plan1207 : Plan := .step choices104 bits449 plan442

def plan1208 : Plan := .step choices104 bits449 plan443

def plan1209 : Plan := .step choices105 bits450 plan431

def plan1210 : Plan := .step choices105 bits450 plan432

def plan1211 : Plan := .step choices105 bits450 plan433

def plan1212 : Plan := .step choices105 bits450 plan434

def plan1213 : Plan := .step choices105 bits450 plan442

def plan1214 : Plan := .step choices105 bits450 plan443

def plan1215 : Plan := .step choices106 bits450 plan434

def plan1216 : Plan := .step choices107 bits446 plan426

def plan1217 : Plan := .step choices107 bits447 plan427

def plan1218 : Plan := .step choices107 bits447 plan428

def plan1219 : Plan := .step choices107 bits446 plan429

def plan1220 : Plan := .step choices107 bits447 plan430

def plan1221 : Plan := .step choices107 bits448 plan431

def plan1222 : Plan := .step choices107 bits448 plan432

def plan1223 : Plan := .step choices107 bits448 plan433

def plan1224 : Plan := .step choices107 bits448 plan434

def plan1225 : Plan := .step choices107 bits446 plan435

def plan1226 : Plan := .step choices107 bits446 plan436

def plan1227 : Plan := .step choices107 bits446 plan437

def plan1228 : Plan := .step choices107 bits447 plan438

def plan1229 : Plan := .step choices107 bits447 plan439

def plan1230 : Plan := .step choices107 bits446 plan440

def plan1231 : Plan := .step choices107 bits447 plan441

def plan1232 : Plan := .step choices107 bits448 plan442

def plan1233 : Plan := .step choices107 bits448 plan443

def plan1234 : Plan := .step choices108 bits449 plan431

def plan1235 : Plan := .step choices108 bits449 plan432

def plan1236 : Plan := .step choices108 bits449 plan433

def plan1237 : Plan := .step choices108 bits449 plan434

def plan1238 : Plan := .step choices108 bits448 plan438

def plan1239 : Plan := .step choices108 bits448 plan439

def plan1240 : Plan := .step choices108 bits447 plan440

def plan1241 : Plan := .step choices108 bits448 plan441

def plan1242 : Plan := .step choices108 bits449 plan442

def plan1243 : Plan := .step choices108 bits449 plan443

def plan1244 : Plan := .step choices109 bits450 plan434

def plan1245 : Plan := .step choices109 bits450 plan442

def plan1246 : Plan := .step choices109 bits450 plan443

def plan1247 : Plan := .step choices112 bits131 plan444

def plan1248 : Plan := .step choices112 bits133 plan445

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


