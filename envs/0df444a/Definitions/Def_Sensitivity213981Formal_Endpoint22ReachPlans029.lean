-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans029
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:46:59.487385+00:00
-- url     : https://prove2.me/theorems/2933e1f2-35be-4287-8ad9-657770dd78ca
-- title:
--   Endpoint22 Reach Plans029 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans029 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2853`, `ThreeBoundEndpoint22Reachable.plan2854`, `ThreeBoundEndpoint22Reachable.plan2855`, `ThreeBoundEndpoint22Reachable.plan2856`, `ThreeBoundEndpoint22Reachable.plan2857`, `ThreeBoundEndpoint22Reachable.plan2858`, `ThreeBoundEndpoint22Reachable.plan2859`, `ThreeBoundEndpoint22Reachable.plan2860`, `ThreeBoundEndpoint22Reachable.plan2790`, `ThreeBoundEndpoint22Reachable.plan2861`, `ThreeBoundEndpoint22Reachable.plan2862`, `ThreeBoundEndpoint22Reachable.plan2863`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans029.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits005
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
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
def plan2785 : Plan := .step choices140 bits677 plan1329

def plan2786 : Plan := .step choices140 bits680 plan1330

def plan2787 : Plan := .step choices140 bits677 plan1332

def plan2788 : Plan := .step choices140 bits679 plan1334

def plan2789 : Plan := .step choices140 bits677 plan1335

def plan2790 : Plan := .step choices140 bits729 plan1336

def plan2791 : Plan := .step choices140 bits730 plan1337

def plan2792 : Plan := .step choices140 bits729 plan1338

def plan2793 : Plan := .step choices140 bits688 plan1339

def plan2794 : Plan := .step choices140 bits689 plan1340

def plan2795 : Plan := .step choices140 bits688 plan1341

def plan2796 : Plan := .step choices140 bits690 plan1342

def plan2797 : Plan := .step choices140 bits689 plan1343

def plan2798 : Plan := .step choices140 bits688 plan1344

def plan2799 : Plan := .step choices140 bits676 plan1345

def plan2800 : Plan := .step choices140 bits728 plan1349

def plan2801 : Plan := .step choices140 bits686 plan1350

def plan2802 : Plan := .step choices140 bits688 plan1351

def plan2803 : Plan := .step choices140 bits686 plan1352

def plan2804 : Plan := .step choices140 bits676 plan1377

def plan2805 : Plan := .step choices140 bits728 plan1381

def plan2806 : Plan := .step choices140 bits686 plan1382

def plan2807 : Plan := .step choices140 bits688 plan1383

def plan2808 : Plan := .step choices140 bits686 plan1384

def plan2809 : Plan := .step choices141 bits737 plan1336

def plan2810 : Plan := .step choices141 bits738 plan1337

def plan2811 : Plan := .step choices141 bits737 plan1338

def plan2812 : Plan := .step choices141 bits698 plan1339

def plan2813 : Plan := .step choices141 bits699 plan1340

def plan2814 : Plan := .step choices141 bits698 plan1341

def plan2815 : Plan := .step choices141 bits700 plan1342

def plan2816 : Plan := .step choices141 bits699 plan1343

def plan2817 : Plan := .step choices141 bits698 plan1344

def plan2818 : Plan := .step choices141 bits736 plan1349

def plan2819 : Plan := .step choices141 bits697 plan1350

def plan2820 : Plan := .step choices141 bits698 plan1351

def plan2821 : Plan := .step choices141 bits697 plan1352

def plan2822 : Plan := .step choices141 bits696 plan1353

def plan2823 : Plan := .step choices141 bits696 plan1363

def plan2824 : Plan := .step choices141 bits736 plan1381

def plan2825 : Plan := .step choices141 bits697 plan1382

def plan2826 : Plan := .step choices141 bits698 plan1383

def plan2827 : Plan := .step choices141 bits697 plan1384

def plan2828 : Plan := .step choices141 bits696 plan1389

def plan2829 : Plan := .step choices144 bits721 plan1320

def plan2830 : Plan := .step choices144 bits722 plan1321

def plan2831 : Plan := .step choices144 bits723 plan1322

def plan2832 : Plan := .step choices144 bits722 plan1323

def plan2833 : Plan := .step choices144 bits677 plan1325

def plan2834 : Plan := .step choices144 bits677 plan1327

def plan2835 : Plan := .step choices144 bits679 plan1328

def plan2836 : Plan := .step choices144 bits677 plan1329

def plan2837 : Plan := .step choices144 bits680 plan1330

def plan2838 : Plan := .step choices144 bits677 plan1332

def plan2839 : Plan := .step choices144 bits679 plan1334

def plan2840 : Plan := .step choices144 bits677 plan1335

def plan2841 : Plan := .step choices144 bits729 plan1336

def plan2842 : Plan := .step choices144 bits730 plan1337

def plan2843 : Plan := .step choices144 bits729 plan1338

def plan2844 : Plan := .step choices144 bits688 plan1339

def plan2845 : Plan := .step choices144 bits689 plan1340

def plan2846 : Plan := .step choices144 bits688 plan1341

def plan2847 : Plan := .step choices144 bits690 plan1342

def plan2848 : Plan := .step choices144 bits689 plan1343

def plan2849 : Plan := .step choices144 bits688 plan1344

def plan2850 : Plan := .step choices144 bits728 plan1349

def plan2851 : Plan := .step choices144 bits686 plan1350

def plan2852 : Plan := .step choices144 bits688 plan1351

def plan2853 : Plan := .step choices144 bits686 plan1352

def plan2854 : Plan := .step choices144 bits676 plan1377

def plan2855 : Plan := .step choices144 bits728 plan1381

def plan2856 : Plan := .step choices144 bits686 plan1382

def plan2857 : Plan := .step choices144 bits688 plan1383

def plan2858 : Plan := .step choices144 bits686 plan1384

def plan2859 : Plan := .step choices145 bits737 plan1336

def plan2860 : Plan := .step choices145 bits738 plan1337

def plan2861 : Plan := .step choices145 bits737 plan1338

def plan2862 : Plan := .step choices145 bits698 plan1339

def plan2863 : Plan := .step choices145 bits699 plan1340

def plan2864 : Plan := .step choices145 bits698 plan1341

def plan2865 : Plan := .step choices145 bits700 plan1342

def plan2866 : Plan := .step choices145 bits699 plan1343

def plan2867 : Plan := .step choices145 bits698 plan1344

def plan2868 : Plan := .step choices145 bits736 plan1381

def plan2869 : Plan := .step choices145 bits697 plan1382

def plan2870 : Plan := .step choices145 bits698 plan1383

def plan2871 : Plan := .step choices145 bits697 plan1384

def plan2872 : Plan := .step choices145 bits696 plan1389

def plan2873 : Plan := .step choices149 bits925 plan1422

def plan2874 : Plan := .step choices149 bits926 plan1423

def plan2875 : Plan := .step choices149 bits925 plan1425

def plan2876 : Plan := .step choices149 bits928 plan1426

def plan2877 : Plan := .step choices149 bits929 plan1427

def plan2878 : Plan := .step choices149 bits928 plan1428

def plan2879 : Plan := .step choices149 bits930 plan1429

def plan2880 : Plan := .step choices149 bits925 plan1431

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


