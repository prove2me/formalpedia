-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans063
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans063
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:01:24.914073+00:00
-- url     : https://prove2.me/theorems/f2d12217-63f5-486b-b3c7-f717a5a66f7c
-- title:
--   Endpoint22 Reach Plans063 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans063 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan6115`, `ThreeBoundEndpoint22Reachable.plan6052`, `ThreeBoundEndpoint22Reachable.plan6116`, `ThreeBoundEndpoint22Reachable.plan6117`, `ThreeBoundEndpoint22Reachable.plan6118`, `ThreeBoundEndpoint22Reachable.plan6119`, `ThreeBoundEndpoint22Reachable.plan6120`, `ThreeBoundEndpoint22Reachable.plan6121`, `ThreeBoundEndpoint22Reachable.plan6122`, `ThreeBoundEndpoint22Reachable.plan6123`, `ThreeBoundEndpoint22Reachable.plan6124`, `ThreeBoundEndpoint22Reachable.plan6125`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans063.lean, lines 1–211.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits003
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits004
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits006
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits010
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans036
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans037
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
def plan6049 : Plan := .step choices226 bits1579 plan3538

def plan6050 : Plan := .step choices226 bits1578 plan3553

def plan6051 : Plan := .step choices226 bits1577 plan3554

def plan6052 : Plan := .step choices226 bits1576 plan3555

def plan6053 : Plan := .step choices226 bits1575 plan3556

def plan6054 : Plan := .step choices227 bits1580 plan3538

def plan6055 : Plan := .step choices228 bits1574 plan3518

def plan6056 : Plan := .step choices228 bits1575 plan3521

def plan6057 : Plan := .step choices228 bits1574 plan3525

def plan6058 : Plan := .step choices228 bits1574 plan3529

def plan6059 : Plan := .step choices228 bits1575 plan3531

def plan6060 : Plan := .step choices228 bits1574 plan3532

def plan6061 : Plan := .step choices228 bits1576 plan3534

def plan6062 : Plan := .step choices228 bits1575 plan3535

def plan6063 : Plan := .step choices228 bits1574 plan3536

def plan6064 : Plan := .step choices228 bits1577 plan3538

def plan6065 : Plan := .step choices228 bits1574 plan3539

def plan6066 : Plan := .step choices228 bits1574 plan3543

def plan6067 : Plan := .step choices228 bits1575 plan3546

def plan6068 : Plan := .step choices228 bits1574 plan3550

def plan6069 : Plan := .step choices228 bits1576 plan3553

def plan6070 : Plan := .step choices228 bits1575 plan3554

def plan6071 : Plan := .step choices228 bits1574 plan3555

def plan6072 : Plan := .step choices229 bits1574 plan3528

def plan6073 : Plan := .step choices229 bits1575 plan3529

def plan6074 : Plan := .step choices229 bits1574 plan3530

def plan6075 : Plan := .step choices229 bits1576 plan3531

def plan6076 : Plan := .step choices229 bits1575 plan3532

def plan6077 : Plan := .step choices229 bits1574 plan3533

def plan6078 : Plan := .step choices229 bits1577 plan3534

def plan6079 : Plan := .step choices229 bits1576 plan3535

def plan6080 : Plan := .step choices229 bits1575 plan3536

def plan6081 : Plan := .step choices229 bits1574 plan3537

def plan6082 : Plan := .step choices229 bits1578 plan3538

def plan6083 : Plan := .step choices229 bits1573 plan3540

def plan6084 : Plan := .step choices229 bits1574 plan3541

def plan6085 : Plan := .step choices229 bits1573 plan3542

def plan6086 : Plan := .step choices229 bits1575 plan3543

def plan6087 : Plan := .step choices229 bits1574 plan3544

def plan6088 : Plan := .step choices229 bits1573 plan3545

def plan6089 : Plan := .step choices229 bits1576 plan3546

def plan6090 : Plan := .step choices229 bits1573 plan3547

def plan6091 : Plan := .step choices229 bits1574 plan3548

def plan6092 : Plan := .step choices229 bits1573 plan3549

def plan6093 : Plan := .step choices229 bits1575 plan3550

def plan6094 : Plan := .step choices229 bits1574 plan3551

def plan6095 : Plan := .step choices229 bits1573 plan3552

def plan6096 : Plan := .step choices229 bits1577 plan3553

def plan6097 : Plan := .step choices229 bits1576 plan3554

def plan6098 : Plan := .step choices229 bits1575 plan3555

def plan6099 : Plan := .step choices229 bits1574 plan3556

def plan6100 : Plan := .step choices230 bits1579 plan3538

def plan6101 : Plan := .step choices230 bits1578 plan3553

def plan6102 : Plan := .step choices230 bits1577 plan3554

def plan6103 : Plan := .step choices230 bits1576 plan3555

def plan6104 : Plan := .step choices230 bits1575 plan3556

def plan6105 : Plan := .step choices231 bits432 plan3557

def plan6106 : Plan := .step choices233 bits616 plan3558

def plan6107 : Plan := .step choices233 bits617 plan3559

def plan6108 : Plan := .step choices233 bits616 plan3560

def plan6109 : Plan := .step choices239 bits923 plan3561

def plan6110 : Plan := .step choices239 bits854 plan3562

def plan6111 : Plan := .step choices239 bits855 plan3563

def plan6112 : Plan := .step choices239 bits854 plan3564

def plan6113 : Plan := .step choices239 bits856 plan3565

def plan6114 : Plan := .step choices239 bits855 plan3566

def plan6115 : Plan := .step choices239 bits854 plan3567

def plan6116 : Plan := .step choices247 bits1074 plan3577

def plan6117 : Plan := .step choices248 bits1111 plan3568

def plan6118 : Plan := .step choices248 bits1112 plan3569

def plan6119 : Plan := .step choices248 bits1111 plan3570

def plan6120 : Plan := .step choices248 bits1075 plan3571

def plan6121 : Plan := .step choices248 bits1076 plan3572

def plan6122 : Plan := .step choices248 bits1075 plan3573

def plan6123 : Plan := .step choices248 bits1077 plan3574

def plan6124 : Plan := .step choices248 bits1076 plan3575

def plan6125 : Plan := .step choices248 bits1075 plan3576

def plan6126 : Plan := .step choices248 bits1078 plan3577

def plan6127 : Plan := .step choices248 bits1077 plan3578

def plan6128 : Plan := .step choices248 bits1076 plan3579

def plan6129 : Plan := .step choices248 bits1075 plan3580

def plan6130 : Plan := .step choices258 bits1276 plan3594

def plan6131 : Plan := .step choices258 bits1277 plan3598

def plan6132 : Plan := .step choices258 bits1276 plan3599

def plan6133 : Plan := .step choices259 bits1323 plan3581

def plan6134 : Plan := .step choices259 bits1319 plan3582

def plan6135 : Plan := .step choices259 bits1320 plan3583

def plan6136 : Plan := .step choices259 bits1319 plan3584

def plan6137 : Plan := .step choices259 bits1321 plan3585

def plan6138 : Plan := .step choices259 bits1320 plan3586

def plan6139 : Plan := .step choices259 bits1319 plan3587

def plan6140 : Plan := .step choices259 bits1278 plan3588

def plan6141 : Plan := .step choices259 bits1279 plan3589

def plan6142 : Plan := .step choices259 bits1278 plan3590

def plan6143 : Plan := .step choices259 bits1280 plan3591

def plan6144 : Plan := .step choices259 bits1279 plan3592

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


