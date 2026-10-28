-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans026
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans026
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:23.271568+00:00
-- url     : https://prove2.me/theorems/361c7647-48e5-43b2-bf27-9d7b2bcdb576
-- title:
--   Endpoint22 Reach Plans026 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans026 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2564`, `ThreeBoundEndpoint22Reachable.plan2565`, `ThreeBoundEndpoint22Reachable.plan2566`, `ThreeBoundEndpoint22Reachable.plan2567`, `ThreeBoundEndpoint22Reachable.plan2501`, `ThreeBoundEndpoint22Reachable.plan2568`, `ThreeBoundEndpoint22Reachable.plan2569`, `ThreeBoundEndpoint22Reachable.plan2570`, `ThreeBoundEndpoint22Reachable.plan2571`, `ThreeBoundEndpoint22Reachable.plan2572`, `ThreeBoundEndpoint22Reachable.plan2573`, `ThreeBoundEndpoint22Reachable.plan2574`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans026.lean, lines 1–208.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits001
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits002
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
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
def plan2497 : Plan := .step choices108 bits861 plan1234

def plan2498 : Plan := .step choices108 bits861 plan1235

def plan2499 : Plan := .step choices108 bits861 plan1236

def plan2500 : Plan := .step choices108 bits861 plan1237

def plan2501 : Plan := .step choices108 bits860 plan1238

def plan2502 : Plan := .step choices108 bits860 plan1239

def plan2503 : Plan := .step choices108 bits859 plan1240

def plan2504 : Plan := .step choices108 bits860 plan1241

def plan2505 : Plan := .step choices108 bits861 plan1242

def plan2506 : Plan := .step choices108 bits861 plan1243

def plan2507 : Plan := .step choices108 bits862 plan1244

def plan2508 : Plan := .step choices108 bits862 plan1245

def plan2509 : Plan := .step choices108 bits862 plan1246

def plan2510 : Plan := .step choices109 bits863 plan1215

def plan2511 : Plan := .step choices109 bits863 plan1244

def plan2512 : Plan := .step choices109 bits863 plan1245

def plan2513 : Plan := .step choices109 bits863 plan1246

def plan2514 : Plan := .step choices111 bits229 plan1249

def plan2515 : Plan := .step choices111 bits230 plan1250

def plan2516 : Plan := .step choices112 bits228 plan1247

def plan2517 : Plan := .step choices112 bits229 plan1248

def plan2518 : Plan := .step choices112 bits230 plan1249

def plan2519 : Plan := .step choices112 bits231 plan1250

def plan2520 : Plan := .step choices113 bits232 plan1250

def plan2521 : Plan := .step choices115 bits369 plan1251

def plan2522 : Plan := .step choices115 bits369 plan1255

def plan2523 : Plan := .step choices115 bits376 plan1259

def plan2524 : Plan := .step choices115 bits380 plan1260

def plan2525 : Plan := .step choices115 bits376 plan1261

def plan2526 : Plan := .step choices115 bits385 plan1265

def plan2527 : Plan := .step choices115 bits386 plan1266

def plan2528 : Plan := .step choices115 bits385 plan1267

def plan2529 : Plan := .step choices115 bits384 plan1268

def plan2530 : Plan := .step choices115 bits384 plan1269

def plan2531 : Plan := .step choices116 bits423 plan1252

def plan2532 : Plan := .step choices116 bits373 plan1253

def plan2533 : Plan := .step choices116 bits376 plan1254

def plan2534 : Plan := .step choices116 bits380 plan1255

def plan2535 : Plan := .step choices116 bits373 plan1256

def plan2536 : Plan := .step choices116 bits376 plan1257

def plan2537 : Plan := .step choices116 bits425 plan1258

def plan2538 : Plan := .step choices116 bits385 plan1259

def plan2539 : Plan := .step choices116 bits386 plan1260

def plan2540 : Plan := .step choices116 bits385 plan1261

def plan2541 : Plan := .step choices116 bits384 plan1262

def plan2542 : Plan := .step choices116 bits384 plan1263

def plan2543 : Plan := .step choices116 bits427 plan1264

def plan2544 : Plan := .step choices116 bits389 plan1265

def plan2545 : Plan := .step choices116 bits390 plan1266

def plan2546 : Plan := .step choices116 bits389 plan1267

def plan2547 : Plan := .step choices116 bits388 plan1268

def plan2548 : Plan := .step choices116 bits388 plan1269

def plan2549 : Plan := .step choices117 bits429 plan1264

def plan2550 : Plan := .step choices117 bits393 plan1265

def plan2551 : Plan := .step choices117 bits394 plan1266

def plan2552 : Plan := .step choices117 bits393 plan1267

def plan2553 : Plan := .step choices118 bits387 plan1258

def plan2554 : Plan := .step choices118 bits391 plan1264

def plan2555 : Plan := .step choices119 bits392 plan1264

def plan2556 : Plan := .step choices122 bits387 plan1258

def plan2557 : Plan := .step choices122 bits391 plan1264

def plan2558 : Plan := .step choices123 bits392 plan1264

def plan2559 : Plan := .step choices126 bits498 plan1270

def plan2560 : Plan := .step choices126 bits499 plan1271

def plan2561 : Plan := .step choices126 bits498 plan1272

def plan2562 : Plan := .step choices126 bits509 plan1283

def plan2563 : Plan := .step choices126 bits511 plan1286

def plan2564 : Plan := .step choices126 bits513 plan1287

def plan2565 : Plan := .step choices126 bits511 plan1288

def plan2566 : Plan := .step choices126 bits514 plan1289

def plan2567 : Plan := .step choices126 bits509 plan1292

def plan2568 : Plan := .step choices126 bits513 plan1295

def plan2569 : Plan := .step choices126 bits511 plan1296

def plan2570 : Plan := .step choices126 bits515 plan1301

def plan2571 : Plan := .step choices126 bits516 plan1302

def plan2572 : Plan := .step choices126 bits515 plan1303

def plan2573 : Plan := .step choices126 bits517 plan1304

def plan2574 : Plan := .step choices126 bits516 plan1305

def plan2575 : Plan := .step choices126 bits515 plan1306

def plan2576 : Plan := .step choices126 bits508 plan1307

def plan2577 : Plan := .step choices126 bits510 plan1309

def plan2578 : Plan := .step choices126 bits512 plan1310

def plan2579 : Plan := .step choices126 bits510 plan1311

def plan2580 : Plan := .step choices126 bits508 plan1314

def plan2581 : Plan := .step choices126 bits510 plan1316

def plan2582 : Plan := .step choices126 bits512 plan1317

def plan2583 : Plan := .step choices126 bits510 plan1318

def plan2584 : Plan := .step choices127 bits568 plan1273

def plan2585 : Plan := .step choices127 bits569 plan1274

def plan2586 : Plan := .step choices127 bits568 plan1275

def plan2587 : Plan := .step choices127 bits572 plan1277

def plan2588 : Plan := .step choices127 bits573 plan1278

def plan2589 : Plan := .step choices127 bits572 plan1279

def plan2590 : Plan := .step choices127 bits567 plan1280

def plan2591 : Plan := .step choices127 bits518 plan1281

def plan2592 : Plan := .step choices127 bits522 plan1282

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


