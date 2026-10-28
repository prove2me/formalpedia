-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans032
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:47:43.053894+00:00
-- url     : https://prove2.me/theorems/0246f2c2-66d7-4859-849b-8370ad52daab
-- title:
--   Endpoint22 Reach Plans032 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans032 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan3141`, `ThreeBoundEndpoint22Reachable.plan3142`, `ThreeBoundEndpoint22Reachable.plan3143`, `ThreeBoundEndpoint22Reachable.plan3144`, `ThreeBoundEndpoint22Reachable.plan3145`, `ThreeBoundEndpoint22Reachable.plan3146`, `ThreeBoundEndpoint22Reachable.plan3147`, `ThreeBoundEndpoint22Reachable.plan3148`, `ThreeBoundEndpoint22Reachable.plan3149`, `ThreeBoundEndpoint22Reachable.plan3078`, `ThreeBoundEndpoint22Reachable.plan3150`, `ThreeBoundEndpoint22Reachable.plan3151`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans032.lean, lines 1–206.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
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
def plan3073 : Plan := .step choices155 bits866 plan1461

def plan3074 : Plan := .step choices155 bits873 plan1462

def plan3075 : Plan := .step choices155 bits871 plan1463

def plan3076 : Plan := .step choices155 bits869 plan1464

def plan3077 : Plan := .step choices156 bits941 plan1407

def plan3078 : Plan := .step choices156 bits942 plan1408

def plan3079 : Plan := .step choices156 bits941 plan1409

def plan3080 : Plan := .step choices156 bits943 plan1410

def plan3081 : Plan := .step choices156 bits942 plan1411

def plan3082 : Plan := .step choices156 bits941 plan1412

def plan3083 : Plan := .step choices156 bits872 plan1437

def plan3084 : Plan := .step choices156 bits874 plan1438

def plan3085 : Plan := .step choices156 bits872 plan1439

def plan3086 : Plan := .step choices156 bits877 plan1440

def plan3087 : Plan := .step choices156 bits874 plan1441

def plan3088 : Plan := .step choices156 bits872 plan1442

def plan3089 : Plan := .step choices156 bits879 plan1443

def plan3090 : Plan := .step choices156 bits938 plan1448

def plan3091 : Plan := .step choices156 bits939 plan1449

def plan3092 : Plan := .step choices156 bits938 plan1450

def plan3093 : Plan := .step choices156 bits869 plan1451

def plan3094 : Plan := .step choices156 bits871 plan1452

def plan3095 : Plan := .step choices156 bits869 plan1453

def plan3096 : Plan := .step choices156 bits873 plan1454

def plan3097 : Plan := .step choices156 bits936 plan1455

def plan3098 : Plan := .step choices156 bits866 plan1456

def plan3099 : Plan := .step choices156 bits868 plan1457

def plan3100 : Plan := .step choices156 bits864 plan1458

def plan3101 : Plan := .step choices156 bits866 plan1459

def plan3102 : Plan := .step choices156 bits871 plan1460

def plan3103 : Plan := .step choices156 bits869 plan1461

def plan3104 : Plan := .step choices156 bits877 plan1462

def plan3105 : Plan := .step choices156 bits874 plan1463

def plan3106 : Plan := .step choices156 bits872 plan1464

def plan3107 : Plan := .step choices157 bits881 plan1443

def plan3108 : Plan := .step choices157 bits880 plan1462

def plan3109 : Plan := .step choices157 bits878 plan1463

def plan3110 : Plan := .step choices157 bits875 plan1464

def plan3111 : Plan := .step choices158 bits1080 plan1465

def plan3112 : Plan := .step choices158 bits1081 plan1466

def plan3113 : Plan := .step choices158 bits1080 plan1467

def plan3114 : Plan := .step choices158 bits1080 plan1470

def plan3115 : Plan := .step choices158 bits1080 plan1473

def plan3116 : Plan := .step choices158 bits1081 plan1474

def plan3117 : Plan := .step choices158 bits1080 plan1475

def plan3118 : Plan := .step choices158 bits1082 plan1476

def plan3119 : Plan := .step choices158 bits1080 plan1478

def plan3120 : Plan := .step choices158 bits1081 plan1481

def plan3121 : Plan := .step choices158 bits1080 plan1482

def plan3122 : Plan := .step choices158 bits1081 plan1483

def plan3123 : Plan := .step choices158 bits1082 plan1484

def plan3124 : Plan := .step choices158 bits1081 plan1485

def plan3125 : Plan := .step choices158 bits1083 plan1486

def plan3126 : Plan := .step choices158 bits1082 plan1487

def plan3127 : Plan := .step choices158 bits1081 plan1488

def plan3128 : Plan := .step choices158 bits1084 plan1489

def plan3129 : Plan := .step choices158 bits1080 plan1490

def plan3130 : Plan := .step choices158 bits1081 plan1491

def plan3131 : Plan := .step choices158 bits1080 plan1492

def plan3132 : Plan := .step choices158 bits1080 plan1493

def plan3133 : Plan := .step choices158 bits1081 plan1494

def plan3134 : Plan := .step choices158 bits1080 plan1495

def plan3135 : Plan := .step choices158 bits1082 plan1496

def plan3136 : Plan := .step choices158 bits1080 plan1498

def plan3137 : Plan := .step choices158 bits1081 plan1501

def plan3138 : Plan := .step choices158 bits1080 plan1502

def plan3139 : Plan := .step choices158 bits1083 plan1503

def plan3140 : Plan := .step choices158 bits1082 plan1504

def plan3141 : Plan := .step choices158 bits1081 plan1505

def plan3142 : Plan := .step choices159 bits1079 plan1468

def plan3143 : Plan := .step choices159 bits1080 plan1469

def plan3144 : Plan := .step choices159 bits1081 plan1470

def plan3145 : Plan := .step choices159 bits1079 plan1471

def plan3146 : Plan := .step choices159 bits1080 plan1472

def plan3147 : Plan := .step choices159 bits1081 plan1473

def plan3148 : Plan := .step choices159 bits1082 plan1474

def plan3149 : Plan := .step choices159 bits1081 plan1475

def plan3150 : Plan := .step choices159 bits1083 plan1476

def plan3151 : Plan := .step choices159 bits1080 plan1477

def plan3152 : Plan := .step choices159 bits1081 plan1478

def plan3153 : Plan := .step choices159 bits1079 plan1479

def plan3154 : Plan := .step choices159 bits1080 plan1480

def plan3155 : Plan := .step choices159 bits1082 plan1481

def plan3156 : Plan := .step choices159 bits1081 plan1482

def plan3157 : Plan := .step choices159 bits1082 plan1483

def plan3158 : Plan := .step choices159 bits1083 plan1484

def plan3159 : Plan := .step choices159 bits1082 plan1485

def plan3160 : Plan := .step choices159 bits1084 plan1486

def plan3161 : Plan := .step choices159 bits1083 plan1487

def plan3162 : Plan := .step choices159 bits1082 plan1488

def plan3163 : Plan := .step choices159 bits1085 plan1489

def plan3164 : Plan := .step choices159 bits1081 plan1493

def plan3165 : Plan := .step choices159 bits1082 plan1494

def plan3166 : Plan := .step choices159 bits1081 plan1495

def plan3167 : Plan := .step choices159 bits1083 plan1496

def plan3168 : Plan := .step choices159 bits1080 plan1497

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


