-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans013
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:45:56.211419+00:00
-- url     : https://prove2.me/theorems/83d66c08-6837-4d6c-a818-0f1b671590be
-- title:
--   Endpoint22 Reach Plans013 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans013 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan1318`, `ThreeBoundEndpoint22Reachable.plan1319`, `ThreeBoundEndpoint22Reachable.plan1320`, `ThreeBoundEndpoint22Reachable.plan1321`, `ThreeBoundEndpoint22Reachable.plan1322`, `ThreeBoundEndpoint22Reachable.plan1323`, `ThreeBoundEndpoint22Reachable.plan1324`, `ThreeBoundEndpoint22Reachable.plan1325`, `ThreeBoundEndpoint22Reachable.plan1326`, `ThreeBoundEndpoint22Reachable.plan1254`, `ThreeBoundEndpoint22Reachable.plan1327`, `ThreeBoundEndpoint22Reachable.plan1328`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans013.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans005
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
def plan1249 : Plan := .step choices112 bits134 plan446

def plan1250 : Plan := .step choices113 bits135 plan446

def plan1251 : Plan := .step choices115 bits190 plan455

def plan1252 : Plan := .step choices116 bits218 plan447

def plan1253 : Plan := .step choices116 bits183 plan448

def plan1254 : Plan := .step choices116 bits187 plan449

def plan1255 : Plan := .step choices116 bits190 plan450

def plan1256 : Plan := .step choices116 bits183 plan451

def plan1257 : Plan := .step choices116 bits187 plan452

def plan1258 : Plan := .step choices116 bits219 plan453

def plan1259 : Plan := .step choices116 bits193 plan454

def plan1260 : Plan := .step choices116 bits194 plan455

def plan1261 : Plan := .step choices116 bits193 plan456

def plan1262 : Plan := .step choices116 bits192 plan457

def plan1263 : Plan := .step choices116 bits192 plan458

def plan1264 : Plan := .step choices117 bits220 plan453

def plan1265 : Plan := .step choices117 bits196 plan454

def plan1266 : Plan := .step choices117 bits197 plan455

def plan1267 : Plan := .step choices117 bits196 plan456

def plan1268 : Plan := .step choices119 bits195 plan453

def plan1269 : Plan := .step choices123 bits195 plan453

def plan1270 : Plan := .step choices126 bits254 plan473

def plan1271 : Plan := .step choices126 bits255 plan475

def plan1272 : Plan := .step choices126 bits254 plan481

def plan1273 : Plan := .step choices127 bits296 plan459

def plan1274 : Plan := .step choices127 bits297 plan460

def plan1275 : Plan := .step choices127 bits296 plan461

def plan1276 : Plan := .step choices127 bits306 plan462

def plan1277 : Plan := .step choices127 bits299 plan463

def plan1278 : Plan := .step choices127 bits300 plan464

def plan1279 : Plan := .step choices127 bits299 plan465

def plan1280 : Plan := .step choices127 bits295 plan466

def plan1281 : Plan := .step choices127 bits256 plan467

def plan1282 : Plan := .step choices127 bits259 plan468

def plan1283 : Plan := .step choices127 bits260 plan469

def plan1284 : Plan := .step choices127 bits256 plan470

def plan1285 : Plan := .step choices127 bits259 plan471

def plan1286 : Plan := .step choices127 bits263 plan472

def plan1287 : Plan := .step choices127 bits264 plan473

def plan1288 : Plan := .step choices127 bits263 plan474

def plan1289 : Plan := .step choices127 bits265 plan475

def plan1290 : Plan := .step choices127 bits295 plan476

def plan1291 : Plan := .step choices127 bits259 plan477

def plan1292 : Plan := .step choices127 bits260 plan478

def plan1293 : Plan := .step choices127 bits256 plan479

def plan1294 : Plan := .step choices127 bits259 plan480

def plan1295 : Plan := .step choices127 bits264 plan481

def plan1296 : Plan := .step choices127 bits263 plan482

def plan1297 : Plan := .step choices128 bits307 plan462

def plan1298 : Plan := .step choices128 bits301 plan463

def plan1299 : Plan := .step choices128 bits302 plan464

def plan1300 : Plan := .step choices128 bits301 plan465

def plan1301 : Plan := .step choices128 bits266 plan472

def plan1302 : Plan := .step choices128 bits267 plan473

def plan1303 : Plan := .step choices128 bits266 plan474

def plan1304 : Plan := .step choices128 bits268 plan475

def plan1305 : Plan := .step choices128 bits267 plan481

def plan1306 : Plan := .step choices128 bits266 plan482

def plan1307 : Plan := .step choices129 bits258 plan464

def plan1308 : Plan := .step choices130 bits298 plan462

def plan1309 : Plan := .step choices130 bits261 plan463

def plan1310 : Plan := .step choices130 bits262 plan464

def plan1311 : Plan := .step choices130 bits261 plan465

def plan1312 : Plan := .step choices130 bits257 plan466

def plan1313 : Plan := .step choices130 bits257 plan476

def plan1314 : Plan := .step choices133 bits258 plan464

def plan1315 : Plan := .step choices134 bits298 plan462

def plan1316 : Plan := .step choices134 bits261 plan463

def plan1317 : Plan := .step choices134 bits262 plan464

def plan1318 : Plan := .step choices134 bits261 plan465

def plan1319 : Plan := .step choices134 bits257 plan476

def plan1320 : Plan := .step choices138 bits433 plan483

def plan1321 : Plan := .step choices138 bits434 plan485

def plan1322 : Plan := .step choices138 bits435 plan486

def plan1323 : Plan := .step choices138 bits434 plan487

def plan1324 : Plan := .step choices138 bits407 plan490

def plan1325 : Plan := .step choices138 bits408 plan491

def plan1326 : Plan := .step choices138 bits407 plan493

def plan1327 : Plan := .step choices138 bits408 plan494

def plan1328 : Plan := .step choices138 bits409 plan495

def plan1329 : Plan := .step choices138 bits408 plan496

def plan1330 : Plan := .step choices138 bits410 plan497

def plan1331 : Plan := .step choices138 bits407 plan499

def plan1332 : Plan := .step choices138 bits408 plan500

def plan1333 : Plan := .step choices138 bits407 plan502

def plan1334 : Plan := .step choices138 bits409 plan503

def plan1335 : Plan := .step choices138 bits408 plan504

def plan1336 : Plan := .step choices139 bits437 plan485

def plan1337 : Plan := .step choices139 bits438 plan486

def plan1338 : Plan := .step choices139 bits437 plan487

def plan1339 : Plan := .step choices139 bits413 plan494

def plan1340 : Plan := .step choices139 bits414 plan495

def plan1341 : Plan := .step choices139 bits413 plan496

def plan1342 : Plan := .step choices139 bits415 plan497

def plan1343 : Plan := .step choices139 bits414 plan503

def plan1344 : Plan := .step choices139 bits413 plan504

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


