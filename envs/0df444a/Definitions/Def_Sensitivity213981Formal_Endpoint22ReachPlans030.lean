-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans030
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:09.087476+00:00
-- url     : https://prove2.me/theorems/43bf4039-661c-48d4-93e5-3ac7e6af7283
-- title:
--   Endpoint22 Reach Plans030 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans030 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan2949`, `ThreeBoundEndpoint22Reachable.plan2950`, `ThreeBoundEndpoint22Reachable.plan2951`, `ThreeBoundEndpoint22Reachable.plan2952`, `ThreeBoundEndpoint22Reachable.plan2953`, `ThreeBoundEndpoint22Reachable.plan2954`, `ThreeBoundEndpoint22Reachable.plan2955`, `ThreeBoundEndpoint22Reachable.plan2956`, `ThreeBoundEndpoint22Reachable.plan2886`, `ThreeBoundEndpoint22Reachable.plan2957`, `ThreeBoundEndpoint22Reachable.plan2958`, `ThreeBoundEndpoint22Reachable.plan2959`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans030.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans014
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans015
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
def plan2881 : Plan := .step choices149 bits926 plan1432

def plan2882 : Plan := .step choices149 bits925 plan1434

def plan2883 : Plan := .step choices149 bits929 plan1435

def plan2884 : Plan := .step choices149 bits928 plan1436

def plan2885 : Plan := .step choices149 bits931 plan1437

def plan2886 : Plan := .step choices149 bits932 plan1438

def plan2887 : Plan := .step choices149 bits931 plan1439

def plan2888 : Plan := .step choices149 bits933 plan1440

def plan2889 : Plan := .step choices149 bits932 plan1441

def plan2890 : Plan := .step choices149 bits931 plan1442

def plan2891 : Plan := .step choices149 bits934 plan1443

def plan2892 : Plan := .step choices149 bits928 plan1451

def plan2893 : Plan := .step choices149 bits929 plan1452

def plan2894 : Plan := .step choices149 bits928 plan1453

def plan2895 : Plan := .step choices149 bits930 plan1454

def plan2896 : Plan := .step choices149 bits925 plan1456

def plan2897 : Plan := .step choices149 bits926 plan1457

def plan2898 : Plan := .step choices149 bits925 plan1459

def plan2899 : Plan := .step choices149 bits929 plan1460

def plan2900 : Plan := .step choices149 bits928 plan1461

def plan2901 : Plan := .step choices149 bits933 plan1462

def plan2902 : Plan := .step choices149 bits932 plan1463

def plan2903 : Plan := .step choices149 bits931 plan1464

def plan2904 : Plan := .step choices150 bits944 plan1437

def plan2905 : Plan := .step choices150 bits945 plan1438

def plan2906 : Plan := .step choices150 bits944 plan1439

def plan2907 : Plan := .step choices150 bits946 plan1440

def plan2908 : Plan := .step choices150 bits945 plan1441

def plan2909 : Plan := .step choices150 bits944 plan1442

def plan2910 : Plan := .step choices150 bits947 plan1443

def plan2911 : Plan := .step choices150 bits946 plan1462

def plan2912 : Plan := .step choices150 bits945 plan1463

def plan2913 : Plan := .step choices150 bits944 plan1464

def plan2914 : Plan := .step choices151 bits924 plan1399

def plan2915 : Plan := .step choices151 bits925 plan1400

def plan2916 : Plan := .step choices151 bits926 plan1401

def plan2917 : Plan := .step choices151 bits925 plan1402

def plan2918 : Plan := .step choices151 bits927 plan1403

def plan2919 : Plan := .step choices151 bits924 plan1404

def plan2920 : Plan := .step choices151 bits926 plan1405

def plan2921 : Plan := .step choices151 bits925 plan1406

def plan2922 : Plan := .step choices151 bits938 plan1407

def plan2923 : Plan := .step choices151 bits939 plan1408

def plan2924 : Plan := .step choices151 bits938 plan1409

def plan2925 : Plan := .step choices151 bits940 plan1410

def plan2926 : Plan := .step choices151 bits939 plan1411

def plan2927 : Plan := .step choices151 bits938 plan1412

def plan2928 : Plan := .step choices151 bits935 plan1413

def plan2929 : Plan := .step choices151 bits865 plan1414

def plan2930 : Plan := .step choices151 bits867 plan1415

def plan2931 : Plan := .step choices151 bits865 plan1416

def plan2932 : Plan := .step choices151 bits936 plan1417

def plan2933 : Plan := .step choices151 bits937 plan1418

def plan2934 : Plan := .step choices151 bits936 plan1419

def plan2935 : Plan := .step choices151 bits865 plan1423

def plan2936 : Plan := .step choices151 bits866 plan1426

def plan2937 : Plan := .step choices151 bits868 plan1427

def plan2938 : Plan := .step choices151 bits866 plan1428

def plan2939 : Plan := .step choices151 bits870 plan1429

def plan2940 : Plan := .step choices151 bits865 plan1432

def plan2941 : Plan := .step choices151 bits868 plan1435

def plan2942 : Plan := .step choices151 bits866 plan1436

def plan2943 : Plan := .step choices151 bits869 plan1437

def plan2944 : Plan := .step choices151 bits871 plan1438

def plan2945 : Plan := .step choices151 bits869 plan1439

def plan2946 : Plan := .step choices151 bits873 plan1440

def plan2947 : Plan := .step choices151 bits871 plan1441

def plan2948 : Plan := .step choices151 bits869 plan1442

def plan2949 : Plan := .step choices151 bits876 plan1443

def plan2950 : Plan := .step choices151 bits935 plan1444

def plan2951 : Plan := .step choices151 bits865 plan1445

def plan2952 : Plan := .step choices151 bits867 plan1446

def plan2953 : Plan := .step choices151 bits865 plan1447

def plan2954 : Plan := .step choices151 bits936 plan1448

def plan2955 : Plan := .step choices151 bits937 plan1449

def plan2956 : Plan := .step choices151 bits936 plan1450

def plan2957 : Plan := .step choices151 bits866 plan1451

def plan2958 : Plan := .step choices151 bits868 plan1452

def plan2959 : Plan := .step choices151 bits866 plan1453

def plan2960 : Plan := .step choices151 bits870 plan1454

def plan2961 : Plan := .step choices151 bits865 plan1457

def plan2962 : Plan := .step choices151 bits868 plan1460

def plan2963 : Plan := .step choices151 bits866 plan1461

def plan2964 : Plan := .step choices151 bits873 plan1462

def plan2965 : Plan := .step choices151 bits871 plan1463

def plan2966 : Plan := .step choices151 bits869 plan1464

def plan2967 : Plan := .step choices152 bits941 plan1407

def plan2968 : Plan := .step choices152 bits942 plan1408

def plan2969 : Plan := .step choices152 bits941 plan1409

def plan2970 : Plan := .step choices152 bits943 plan1410

def plan2971 : Plan := .step choices152 bits942 plan1411

def plan2972 : Plan := .step choices152 bits941 plan1412

def plan2973 : Plan := .step choices152 bits938 plan1417

def plan2974 : Plan := .step choices152 bits939 plan1418

def plan2975 : Plan := .step choices152 bits938 plan1419

def plan2976 : Plan := .step choices152 bits936 plan1420

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


