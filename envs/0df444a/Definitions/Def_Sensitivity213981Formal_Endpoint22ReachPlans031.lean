-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans031
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:23.601238+00:00
-- url     : https://prove2.me/theorems/7dbaee5f-2dee-4c68-bfeb-4fc89a6f62c6
-- title:
--   Endpoint22 Reach Plans031 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans031 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3045`, `ThreeBoundEndpoint22Reachable.plan3046`, `ThreeBoundEndpoint22Reachable.plan3047`, `ThreeBoundEndpoint22Reachable.plan3048`, `ThreeBoundEndpoint22Reachable.plan3049`, `ThreeBoundEndpoint22Reachable.plan3050`, `ThreeBoundEndpoint22Reachable.plan3051`, `ThreeBoundEndpoint22Reachable.plan3052`, `ThreeBoundEndpoint22Reachable.plan2982`, `ThreeBoundEndpoint22Reachable.plan3053`, `ThreeBoundEndpoint22Reachable.plan3054`, `ThreeBoundEndpoint22Reachable.plan3055`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans031.lean, lines 1–205.

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
def plan2977 : Plan := .step choices152 bits864 plan1421

def plan2978 : Plan := .step choices152 bits866 plan1422

def plan2979 : Plan := .step choices152 bits868 plan1423

def plan2980 : Plan := .step choices152 bits864 plan1424

def plan2981 : Plan := .step choices152 bits866 plan1425

def plan2982 : Plan := .step choices152 bits869 plan1426

def plan2983 : Plan := .step choices152 bits871 plan1427

def plan2984 : Plan := .step choices152 bits869 plan1428

def plan2985 : Plan := .step choices152 bits873 plan1429

def plan2986 : Plan := .step choices152 bits936 plan1430

def plan2987 : Plan := .step choices152 bits866 plan1431

def plan2988 : Plan := .step choices152 bits868 plan1432

def plan2989 : Plan := .step choices152 bits864 plan1433

def plan2990 : Plan := .step choices152 bits866 plan1434

def plan2991 : Plan := .step choices152 bits871 plan1435

def plan2992 : Plan := .step choices152 bits869 plan1436

def plan2993 : Plan := .step choices152 bits872 plan1437

def plan2994 : Plan := .step choices152 bits874 plan1438

def plan2995 : Plan := .step choices152 bits872 plan1439

def plan2996 : Plan := .step choices152 bits877 plan1440

def plan2997 : Plan := .step choices152 bits874 plan1441

def plan2998 : Plan := .step choices152 bits872 plan1442

def plan2999 : Plan := .step choices152 bits879 plan1443

def plan3000 : Plan := .step choices152 bits938 plan1448

def plan3001 : Plan := .step choices152 bits939 plan1449

def plan3002 : Plan := .step choices152 bits938 plan1450

def plan3003 : Plan := .step choices152 bits869 plan1451

def plan3004 : Plan := .step choices152 bits871 plan1452

def plan3005 : Plan := .step choices152 bits869 plan1453

def plan3006 : Plan := .step choices152 bits873 plan1454

def plan3007 : Plan := .step choices152 bits936 plan1455

def plan3008 : Plan := .step choices152 bits866 plan1456

def plan3009 : Plan := .step choices152 bits868 plan1457

def plan3010 : Plan := .step choices152 bits864 plan1458

def plan3011 : Plan := .step choices152 bits866 plan1459

def plan3012 : Plan := .step choices152 bits871 plan1460

def plan3013 : Plan := .step choices152 bits869 plan1461

def plan3014 : Plan := .step choices152 bits877 plan1462

def plan3015 : Plan := .step choices152 bits874 plan1463

def plan3016 : Plan := .step choices152 bits872 plan1464

def plan3017 : Plan := .step choices153 bits875 plan1437

def plan3018 : Plan := .step choices153 bits878 plan1438

def plan3019 : Plan := .step choices153 bits875 plan1439

def plan3020 : Plan := .step choices153 bits880 plan1440

def plan3021 : Plan := .step choices153 bits878 plan1441

def plan3022 : Plan := .step choices153 bits875 plan1442

def plan3023 : Plan := .step choices153 bits881 plan1443

def plan3024 : Plan := .step choices153 bits880 plan1462

def plan3025 : Plan := .step choices153 bits878 plan1463

def plan3026 : Plan := .step choices153 bits875 plan1464

def plan3027 : Plan := .step choices154 bits882 plan1443

def plan3028 : Plan := .step choices155 bits924 plan1399

def plan3029 : Plan := .step choices155 bits925 plan1400

def plan3030 : Plan := .step choices155 bits926 plan1401

def plan3031 : Plan := .step choices155 bits925 plan1402

def plan3032 : Plan := .step choices155 bits927 plan1403

def plan3033 : Plan := .step choices155 bits924 plan1404

def plan3034 : Plan := .step choices155 bits926 plan1405

def plan3035 : Plan := .step choices155 bits925 plan1406

def plan3036 : Plan := .step choices155 bits938 plan1407

def plan3037 : Plan := .step choices155 bits939 plan1408

def plan3038 : Plan := .step choices155 bits938 plan1409

def plan3039 : Plan := .step choices155 bits940 plan1410

def plan3040 : Plan := .step choices155 bits939 plan1411

def plan3041 : Plan := .step choices155 bits938 plan1412

def plan3042 : Plan := .step choices155 bits936 plan1417

def plan3043 : Plan := .step choices155 bits937 plan1418

def plan3044 : Plan := .step choices155 bits936 plan1419

def plan3045 : Plan := .step choices155 bits865 plan1423

def plan3046 : Plan := .step choices155 bits866 plan1426

def plan3047 : Plan := .step choices155 bits868 plan1427

def plan3048 : Plan := .step choices155 bits866 plan1428

def plan3049 : Plan := .step choices155 bits870 plan1429

def plan3050 : Plan := .step choices155 bits865 plan1432

def plan3051 : Plan := .step choices155 bits868 plan1435

def plan3052 : Plan := .step choices155 bits866 plan1436

def plan3053 : Plan := .step choices155 bits869 plan1437

def plan3054 : Plan := .step choices155 bits871 plan1438

def plan3055 : Plan := .step choices155 bits869 plan1439

def plan3056 : Plan := .step choices155 bits873 plan1440

def plan3057 : Plan := .step choices155 bits871 plan1441

def plan3058 : Plan := .step choices155 bits869 plan1442

def plan3059 : Plan := .step choices155 bits876 plan1443

def plan3060 : Plan := .step choices155 bits935 plan1444

def plan3061 : Plan := .step choices155 bits865 plan1445

def plan3062 : Plan := .step choices155 bits867 plan1446

def plan3063 : Plan := .step choices155 bits865 plan1447

def plan3064 : Plan := .step choices155 bits936 plan1448

def plan3065 : Plan := .step choices155 bits937 plan1449

def plan3066 : Plan := .step choices155 bits936 plan1450

def plan3067 : Plan := .step choices155 bits866 plan1451

def plan3068 : Plan := .step choices155 bits868 plan1452

def plan3069 : Plan := .step choices155 bits866 plan1453

def plan3070 : Plan := .step choices155 bits870 plan1454

def plan3071 : Plan := .step choices155 bits865 plan1457

def plan3072 : Plan := .step choices155 bits868 plan1460

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


