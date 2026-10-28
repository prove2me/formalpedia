-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans028
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:24.246265+00:00
-- url     : https://prove2.me/theorems/ad45f853-2bfd-4c5c-9119-19b02cb021d7
-- title:
--   Endpoint22 Reach Plans028 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans028 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2757`, `ThreeBoundEndpoint22Reachable.plan2758`, `ThreeBoundEndpoint22Reachable.plan2759`, `ThreeBoundEndpoint22Reachable.plan2760`, `ThreeBoundEndpoint22Reachable.plan2761`, `ThreeBoundEndpoint22Reachable.plan2762`, `ThreeBoundEndpoint22Reachable.plan2694`, `ThreeBoundEndpoint22Reachable.plan2763`, `ThreeBoundEndpoint22Reachable.plan2764`, `ThreeBoundEndpoint22Reachable.plan2765`, `ThreeBoundEndpoint22Reachable.plan2766`, `ThreeBoundEndpoint22Reachable.plan2767`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans028.lean, lines 1–204.

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
def plan2689 : Plan := .step choices137 bits674 plan1380

def plan2690 : Plan := .step choices137 bits678 plan1385

def plan2691 : Plan := .step choices137 bits681 plan1386

def plan2692 : Plan := .step choices137 bits678 plan1387

def plan2693 : Plan := .step choices137 bits682 plan1388

def plan2694 : Plan := .step choices137 bits678 plan1391

def plan2695 : Plan := .step choices137 bits681 plan1394

def plan2696 : Plan := .step choices137 bits678 plan1395

def plan2697 : Plan := .step choices137 bits683 plan1396

def plan2698 : Plan := .step choices137 bits682 plan1397

def plan2699 : Plan := .step choices137 bits681 plan1398

def plan2700 : Plan := .step choices138 bits724 plan1324

def plan2701 : Plan := .step choices138 bits725 plan1325

def plan2702 : Plan := .step choices138 bits724 plan1326

def plan2703 : Plan := .step choices138 bits725 plan1327

def plan2704 : Plan := .step choices138 bits726 plan1328

def plan2705 : Plan := .step choices138 bits725 plan1329

def plan2706 : Plan := .step choices138 bits727 plan1330

def plan2707 : Plan := .step choices138 bits724 plan1331

def plan2708 : Plan := .step choices138 bits725 plan1332

def plan2709 : Plan := .step choices138 bits724 plan1333

def plan2710 : Plan := .step choices138 bits726 plan1334

def plan2711 : Plan := .step choices138 bits725 plan1335

def plan2712 : Plan := .step choices138 bits733 plan1339

def plan2713 : Plan := .step choices138 bits734 plan1340

def plan2714 : Plan := .step choices138 bits733 plan1341

def plan2715 : Plan := .step choices138 bits735 plan1342

def plan2716 : Plan := .step choices138 bits734 plan1343

def plan2717 : Plan := .step choices138 bits733 plan1344

def plan2718 : Plan := .step choices138 bits732 plan1350

def plan2719 : Plan := .step choices138 bits733 plan1351

def plan2720 : Plan := .step choices138 bits732 plan1352

def plan2721 : Plan := .step choices138 bits731 plan1353

def plan2722 : Plan := .step choices138 bits685 plan1354

def plan2723 : Plan := .step choices138 bits687 plan1355

def plan2724 : Plan := .step choices138 bits691 plan1356

def plan2725 : Plan := .step choices138 bits685 plan1357

def plan2726 : Plan := .step choices138 bits687 plan1358

def plan2727 : Plan := .step choices138 bits691 plan1359

def plan2728 : Plan := .step choices138 bits692 plan1360

def plan2729 : Plan := .step choices138 bits691 plan1361

def plan2730 : Plan := .step choices138 bits693 plan1362

def plan2731 : Plan := .step choices138 bits731 plan1363

def plan2732 : Plan := .step choices138 bits687 plan1364

def plan2733 : Plan := .step choices138 bits691 plan1365

def plan2734 : Plan := .step choices138 bits685 plan1366

def plan2735 : Plan := .step choices138 bits687 plan1367

def plan2736 : Plan := .step choices138 bits692 plan1368

def plan2737 : Plan := .step choices138 bits691 plan1369

def plan2738 : Plan := .step choices138 bits692 plan1370

def plan2739 : Plan := .step choices138 bits693 plan1371

def plan2740 : Plan := .step choices138 bits692 plan1372

def plan2741 : Plan := .step choices138 bits694 plan1373

def plan2742 : Plan := .step choices138 bits693 plan1374

def plan2743 : Plan := .step choices138 bits692 plan1375

def plan2744 : Plan := .step choices138 bits695 plan1376

def plan2745 : Plan := .step choices138 bits732 plan1382

def plan2746 : Plan := .step choices138 bits733 plan1383

def plan2747 : Plan := .step choices138 bits732 plan1384

def plan2748 : Plan := .step choices138 bits691 plan1385

def plan2749 : Plan := .step choices138 bits692 plan1386

def plan2750 : Plan := .step choices138 bits691 plan1387

def plan2751 : Plan := .step choices138 bits693 plan1388

def plan2752 : Plan := .step choices138 bits731 plan1389

def plan2753 : Plan := .step choices138 bits687 plan1390

def plan2754 : Plan := .step choices138 bits691 plan1391

def plan2755 : Plan := .step choices138 bits685 plan1392

def plan2756 : Plan := .step choices138 bits687 plan1393

def plan2757 : Plan := .step choices138 bits692 plan1394

def plan2758 : Plan := .step choices138 bits691 plan1395

def plan2759 : Plan := .step choices138 bits694 plan1396

def plan2760 : Plan := .step choices138 bits693 plan1397

def plan2761 : Plan := .step choices138 bits692 plan1398

def plan2762 : Plan := .step choices139 bits738 plan1339

def plan2763 : Plan := .step choices139 bits739 plan1340

def plan2764 : Plan := .step choices139 bits738 plan1341

def plan2765 : Plan := .step choices139 bits740 plan1342

def plan2766 : Plan := .step choices139 bits739 plan1343

def plan2767 : Plan := .step choices139 bits738 plan1344

def plan2768 : Plan := .step choices139 bits699 plan1370

def plan2769 : Plan := .step choices139 bits700 plan1371

def plan2770 : Plan := .step choices139 bits699 plan1372

def plan2771 : Plan := .step choices139 bits701 plan1373

def plan2772 : Plan := .step choices139 bits700 plan1374

def plan2773 : Plan := .step choices139 bits699 plan1375

def plan2774 : Plan := .step choices139 bits702 plan1376

def plan2775 : Plan := .step choices139 bits701 plan1396

def plan2776 : Plan := .step choices139 bits700 plan1397

def plan2777 : Plan := .step choices139 bits699 plan1398

def plan2778 : Plan := .step choices140 bits721 plan1320

def plan2779 : Plan := .step choices140 bits722 plan1321

def plan2780 : Plan := .step choices140 bits723 plan1322

def plan2781 : Plan := .step choices140 bits722 plan1323

def plan2782 : Plan := .step choices140 bits677 plan1325

def plan2783 : Plan := .step choices140 bits677 plan1327

def plan2784 : Plan := .step choices140 bits679 plan1328

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


