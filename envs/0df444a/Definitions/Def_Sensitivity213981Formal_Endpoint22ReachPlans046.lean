-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans046
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans046
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:48:38.718275+00:00
-- url     : https://prove2.me/theorems/78b8d939-fa5e-45b9-91b0-d6a79fc56a71
-- title:
--   Endpoint22 Reach Plans046 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans046 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4484`, `ThreeBoundEndpoint22Reachable.plan4485`, `ThreeBoundEndpoint22Reachable.plan4486`, `ThreeBoundEndpoint22Reachable.plan4487`, `ThreeBoundEndpoint22Reachable.plan4421`, `ThreeBoundEndpoint22Reachable.plan4488`, `ThreeBoundEndpoint22Reachable.plan4489`, `ThreeBoundEndpoint22Reachable.plan4490`, `ThreeBoundEndpoint22Reachable.plan4491`, `ThreeBoundEndpoint22Reachable.plan4492`, `ThreeBoundEndpoint22Reachable.plan4493`, `ThreeBoundEndpoint22Reachable.plan4494`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans046.lean, lines 1–208.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
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
def plan4417 : Plan := .step choices144 bits1037 plan2763

def plan4418 : Plan := .step choices144 bits1036 plan2764

def plan4419 : Plan := .step choices144 bits1038 plan2765

def plan4420 : Plan := .step choices144 bits1037 plan2766

def plan4421 : Plan := .step choices144 bits1036 plan2767

def plan4422 : Plan := .step choices144 bits1035 plan2809

def plan4423 : Plan := .step choices144 bits1036 plan2810

def plan4424 : Plan := .step choices144 bits1035 plan2811

def plan4425 : Plan := .step choices144 bits1033 plan2818

def plan4426 : Plan := .step choices144 bits1033 plan2824

def plan4427 : Plan := .step choices144 bits997 plan2829

def plan4428 : Plan := .step choices144 bits1006 plan2830

def plan4429 : Plan := .step choices144 bits1007 plan2831

def plan4430 : Plan := .step choices144 bits1006 plan2832

def plan4431 : Plan := .step choices144 bits1021 plan2841

def plan4432 : Plan := .step choices144 bits1022 plan2842

def plan4433 : Plan := .step choices144 bits1021 plan2843

def plan4434 : Plan := .step choices144 bits1018 plan2850

def plan4435 : Plan := .step choices144 bits1018 plan2855

def plan4436 : Plan := .step choices144 bits1035 plan2859

def plan4437 : Plan := .step choices144 bits1036 plan2860

def plan4438 : Plan := .step choices144 bits1035 plan2861

def plan4439 : Plan := .step choices144 bits1033 plan2868

def plan4440 : Plan := .step choices145 bits1047 plan2762

def plan4441 : Plan := .step choices145 bits1048 plan2763

def plan4442 : Plan := .step choices145 bits1047 plan2764

def plan4443 : Plan := .step choices145 bits1049 plan2765

def plan4444 : Plan := .step choices145 bits1048 plan2766

def plan4445 : Plan := .step choices145 bits1047 plan2767

def plan4446 : Plan := .step choices145 bits1046 plan2859

def plan4447 : Plan := .step choices145 bits1047 plan2860

def plan4448 : Plan := .step choices145 bits1046 plan2861

def plan4449 : Plan := .step choices145 bits1045 plan2868

def plan4450 : Plan := .step choices147 bits1164 plan2937

def plan4451 : Plan := .step choices147 bits1166 plan2939

def plan4452 : Plan := .step choices147 bits1164 plan2941

def plan4453 : Plan := .step choices147 bits1165 plan2943

def plan4454 : Plan := .step choices147 bits1167 plan2944

def plan4455 : Plan := .step choices147 bits1165 plan2945

def plan4456 : Plan := .step choices147 bits1169 plan2946

def plan4457 : Plan := .step choices147 bits1167 plan2947

def plan4458 : Plan := .step choices147 bits1165 plan2948

def plan4459 : Plan := .step choices147 bits1172 plan2949

def plan4460 : Plan := .step choices147 bits1164 plan2958

def plan4461 : Plan := .step choices147 bits1166 plan2960

def plan4462 : Plan := .step choices147 bits1164 plan2962

def plan4463 : Plan := .step choices147 bits1169 plan2964

def plan4464 : Plan := .step choices147 bits1167 plan2965

def plan4465 : Plan := .step choices147 bits1165 plan2966

def plan4466 : Plan := .step choices147 bits1164 plan2979

def plan4467 : Plan := .step choices147 bits1165 plan2982

def plan4468 : Plan := .step choices147 bits1167 plan2983

def plan4469 : Plan := .step choices147 bits1165 plan2984

def plan4470 : Plan := .step choices147 bits1169 plan2985

def plan4471 : Plan := .step choices147 bits1164 plan2988

def plan4472 : Plan := .step choices147 bits1167 plan2991

def plan4473 : Plan := .step choices147 bits1165 plan2992

def plan4474 : Plan := .step choices147 bits1168 plan2993

def plan4475 : Plan := .step choices147 bits1170 plan2994

def plan4476 : Plan := .step choices147 bits1168 plan2995

def plan4477 : Plan := .step choices147 bits1173 plan2996

def plan4478 : Plan := .step choices147 bits1170 plan2997

def plan4479 : Plan := .step choices147 bits1168 plan2998

def plan4480 : Plan := .step choices147 bits1175 plan2999

def plan4481 : Plan := .step choices147 bits1165 plan3003

def plan4482 : Plan := .step choices147 bits1167 plan3004

def plan4483 : Plan := .step choices147 bits1165 plan3005

def plan4484 : Plan := .step choices147 bits1169 plan3006

def plan4485 : Plan := .step choices147 bits1164 plan3009

def plan4486 : Plan := .step choices147 bits1167 plan3012

def plan4487 : Plan := .step choices147 bits1165 plan3013

def plan4488 : Plan := .step choices147 bits1173 plan3014

def plan4489 : Plan := .step choices147 bits1170 plan3015

def plan4490 : Plan := .step choices147 bits1168 plan3016

def plan4491 : Plan := .step choices147 bits1171 plan3017

def plan4492 : Plan := .step choices147 bits1174 plan3018

def plan4493 : Plan := .step choices147 bits1171 plan3019

def plan4494 : Plan := .step choices147 bits1176 plan3020

def plan4495 : Plan := .step choices147 bits1174 plan3021

def plan4496 : Plan := .step choices147 bits1171 plan3022

def plan4497 : Plan := .step choices147 bits1177 plan3023

def plan4498 : Plan := .step choices147 bits1176 plan3024

def plan4499 : Plan := .step choices147 bits1174 plan3025

def plan4500 : Plan := .step choices147 bits1171 plan3026

def plan4501 : Plan := .step choices147 bits1178 plan3027

def plan4502 : Plan := .step choices147 bits1164 plan3047

def plan4503 : Plan := .step choices147 bits1166 plan3049

def plan4504 : Plan := .step choices147 bits1164 plan3051

def plan4505 : Plan := .step choices147 bits1165 plan3053

def plan4506 : Plan := .step choices147 bits1167 plan3054

def plan4507 : Plan := .step choices147 bits1165 plan3055

def plan4508 : Plan := .step choices147 bits1169 plan3056

def plan4509 : Plan := .step choices147 bits1167 plan3057

def plan4510 : Plan := .step choices147 bits1165 plan3058

def plan4511 : Plan := .step choices147 bits1172 plan3059

def plan4512 : Plan := .step choices147 bits1164 plan3068

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


