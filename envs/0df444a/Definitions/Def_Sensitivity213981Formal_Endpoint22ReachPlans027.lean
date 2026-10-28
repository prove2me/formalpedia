-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans027
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans027
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:03.589361+00:00
-- url     : https://prove2.me/theorems/562e5f4a-5b54-40d0-8bda-1ef5667b0f4f
-- title:
--   Endpoint22 Reach Plans027 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans027 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2661`, `ThreeBoundEndpoint22Reachable.plan2662`, `ThreeBoundEndpoint22Reachable.plan2663`, `ThreeBoundEndpoint22Reachable.plan2664`, `ThreeBoundEndpoint22Reachable.plan2665`, `ThreeBoundEndpoint22Reachable.plan2666`, `ThreeBoundEndpoint22Reachable.plan2667`, `ThreeBoundEndpoint22Reachable.plan2668`, `ThreeBoundEndpoint22Reachable.plan2598`, `ThreeBoundEndpoint22Reachable.plan2669`, `ThreeBoundEndpoint22Reachable.plan2670`, `ThreeBoundEndpoint22Reachable.plan2671`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans027.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
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
def plan2593 : Plan := .step choices127 bits524 plan1283

def plan2594 : Plan := .step choices127 bits518 plan1284

def plan2595 : Plan := .step choices127 bits522 plan1285

def plan2596 : Plan := .step choices127 bits527 plan1286

def plan2597 : Plan := .step choices127 bits530 plan1287

def plan2598 : Plan := .step choices127 bits527 plan1288

def plan2599 : Plan := .step choices127 bits531 plan1289

def plan2600 : Plan := .step choices127 bits567 plan1290

def plan2601 : Plan := .step choices127 bits522 plan1291

def plan2602 : Plan := .step choices127 bits524 plan1292

def plan2603 : Plan := .step choices127 bits518 plan1293

def plan2604 : Plan := .step choices127 bits522 plan1294

def plan2605 : Plan := .step choices127 bits530 plan1295

def plan2606 : Plan := .step choices127 bits527 plan1296

def plan2607 : Plan := .step choices127 bits575 plan1298

def plan2608 : Plan := .step choices127 bits576 plan1299

def plan2609 : Plan := .step choices127 bits575 plan1300

def plan2610 : Plan := .step choices127 bits533 plan1301

def plan2611 : Plan := .step choices127 bits536 plan1302

def plan2612 : Plan := .step choices127 bits533 plan1303

def plan2613 : Plan := .step choices127 bits537 plan1304

def plan2614 : Plan := .step choices127 bits536 plan1305

def plan2615 : Plan := .step choices127 bits533 plan1306

def plan2616 : Plan := .step choices127 bits571 plan1308

def plan2617 : Plan := .step choices127 bits526 plan1309

def plan2618 : Plan := .step choices127 bits529 plan1310

def plan2619 : Plan := .step choices127 bits526 plan1311

def plan2620 : Plan := .step choices127 bits521 plan1312

def plan2621 : Plan := .step choices127 bits521 plan1313

def plan2622 : Plan := .step choices127 bits571 plan1315

def plan2623 : Plan := .step choices127 bits526 plan1316

def plan2624 : Plan := .step choices127 bits529 plan1317

def plan2625 : Plan := .step choices127 bits526 plan1318

def plan2626 : Plan := .step choices127 bits521 plan1319

def plan2627 : Plan := .step choices128 bits577 plan1298

def plan2628 : Plan := .step choices128 bits578 plan1299

def plan2629 : Plan := .step choices128 bits577 plan1300

def plan2630 : Plan := .step choices128 bits538 plan1301

def plan2631 : Plan := .step choices128 bits540 plan1302

def plan2632 : Plan := .step choices128 bits538 plan1303

def plan2633 : Plan := .step choices128 bits541 plan1304

def plan2634 : Plan := .step choices128 bits540 plan1305

def plan2635 : Plan := .step choices128 bits538 plan1306

def plan2636 : Plan := .step choices129 bits519 plan1274

def plan2637 : Plan := .step choices129 bits566 plan1276

def plan2638 : Plan := .step choices129 bits521 plan1277

def plan2639 : Plan := .step choices129 bits523 plan1278

def plan2640 : Plan := .step choices129 bits521 plan1279

def plan2641 : Plan := .step choices129 bits570 plan1297

def plan2642 : Plan := .step choices129 bits525 plan1298

def plan2643 : Plan := .step choices129 bits528 plan1299

def plan2644 : Plan := .step choices129 bits525 plan1300

def plan2645 : Plan := .step choices129 bits520 plan1308

def plan2646 : Plan := .step choices129 bits520 plan1315

def plan2647 : Plan := .step choices130 bits574 plan1297

def plan2648 : Plan := .step choices130 bits532 plan1298

def plan2649 : Plan := .step choices130 bits535 plan1299

def plan2650 : Plan := .step choices130 bits532 plan1300

def plan2651 : Plan := .step choices130 bits525 plan1308

def plan2652 : Plan := .step choices130 bits525 plan1315

def plan2653 : Plan := .step choices133 bits519 plan1274

def plan2654 : Plan := .step choices133 bits566 plan1276

def plan2655 : Plan := .step choices133 bits521 plan1277

def plan2656 : Plan := .step choices133 bits523 plan1278

def plan2657 : Plan := .step choices133 bits521 plan1279

def plan2658 : Plan := .step choices133 bits570 plan1297

def plan2659 : Plan := .step choices133 bits525 plan1298

def plan2660 : Plan := .step choices133 bits528 plan1299

def plan2661 : Plan := .step choices133 bits525 plan1300

def plan2662 : Plan := .step choices133 bits520 plan1308

def plan2663 : Plan := .step choices133 bits520 plan1315

def plan2664 : Plan := .step choices134 bits574 plan1297

def plan2665 : Plan := .step choices134 bits532 plan1298

def plan2666 : Plan := .step choices134 bits535 plan1299

def plan2667 : Plan := .step choices134 bits532 plan1300

def plan2668 : Plan := .step choices134 bits525 plan1315

def plan2669 : Plan := .step choices137 bits674 plan1346

def plan2670 : Plan := .step choices137 bits675 plan1347

def plan2671 : Plan := .step choices137 bits674 plan1348

def plan2672 : Plan := .step choices137 bits678 plan1356

def plan2673 : Plan := .step choices137 bits678 plan1359

def plan2674 : Plan := .step choices137 bits681 plan1360

def plan2675 : Plan := .step choices137 bits678 plan1361

def plan2676 : Plan := .step choices137 bits682 plan1362

def plan2677 : Plan := .step choices137 bits678 plan1365

def plan2678 : Plan := .step choices137 bits681 plan1368

def plan2679 : Plan := .step choices137 bits678 plan1369

def plan2680 : Plan := .step choices137 bits681 plan1370

def plan2681 : Plan := .step choices137 bits682 plan1371

def plan2682 : Plan := .step choices137 bits681 plan1372

def plan2683 : Plan := .step choices137 bits683 plan1373

def plan2684 : Plan := .step choices137 bits682 plan1374

def plan2685 : Plan := .step choices137 bits681 plan1375

def plan2686 : Plan := .step choices137 bits684 plan1376

def plan2687 : Plan := .step choices137 bits674 plan1378

def plan2688 : Plan := .step choices137 bits675 plan1379

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


