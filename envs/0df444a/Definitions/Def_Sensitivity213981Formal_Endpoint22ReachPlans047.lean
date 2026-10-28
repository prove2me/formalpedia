-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans047
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans047
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:48:56.401411+00:00
-- url     : https://prove2.me/theorems/c545aa30-5cf3-465a-8ed2-1a99a543779f
-- title:
--   Endpoint22 Reach Plans047 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans047 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4581`, `ThreeBoundEndpoint22Reachable.plan4582`, `ThreeBoundEndpoint22Reachable.plan4583`, `ThreeBoundEndpoint22Reachable.plan4584`, `ThreeBoundEndpoint22Reachable.plan4585`, `ThreeBoundEndpoint22Reachable.plan4586`, `ThreeBoundEndpoint22Reachable.plan4587`, `ThreeBoundEndpoint22Reachable.plan4518`, `ThreeBoundEndpoint22Reachable.plan4588`, `ThreeBoundEndpoint22Reachable.plan4589`, `ThreeBoundEndpoint22Reachable.plan4590`, `ThreeBoundEndpoint22Reachable.plan4591`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans047.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans030
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans031
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans032
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
def plan4513 : Plan := .step choices147 bits1166 plan3070

def plan4514 : Plan := .step choices147 bits1164 plan3072

def plan4515 : Plan := .step choices147 bits1169 plan3074

def plan4516 : Plan := .step choices147 bits1167 plan3075

def plan4517 : Plan := .step choices147 bits1165 plan3076

def plan4518 : Plan := .step choices147 bits1168 plan3083

def plan4519 : Plan := .step choices147 bits1170 plan3084

def plan4520 : Plan := .step choices147 bits1168 plan3085

def plan4521 : Plan := .step choices147 bits1173 plan3086

def plan4522 : Plan := .step choices147 bits1170 plan3087

def plan4523 : Plan := .step choices147 bits1168 plan3088

def plan4524 : Plan := .step choices147 bits1175 plan3089

def plan4525 : Plan := .step choices147 bits1165 plan3093

def plan4526 : Plan := .step choices147 bits1167 plan3094

def plan4527 : Plan := .step choices147 bits1165 plan3095

def plan4528 : Plan := .step choices147 bits1169 plan3096

def plan4529 : Plan := .step choices147 bits1164 plan3099

def plan4530 : Plan := .step choices147 bits1167 plan3102

def plan4531 : Plan := .step choices147 bits1165 plan3103

def plan4532 : Plan := .step choices147 bits1173 plan3104

def plan4533 : Plan := .step choices147 bits1170 plan3105

def plan4534 : Plan := .step choices147 bits1168 plan3106

def plan4535 : Plan := .step choices147 bits1177 plan3107

def plan4536 : Plan := .step choices147 bits1176 plan3108

def plan4537 : Plan := .step choices147 bits1174 plan3109

def plan4538 : Plan := .step choices147 bits1171 plan3110

def plan4539 : Plan := .step choices148 bits1179 plan2929

def plan4540 : Plan := .step choices148 bits1181 plan2930

def plan4541 : Plan := .step choices148 bits1179 plan2931

def plan4542 : Plan := .step choices148 bits1179 plan2935

def plan4543 : Plan := .step choices148 bits1180 plan2936

def plan4544 : Plan := .step choices148 bits1182 plan2937

def plan4545 : Plan := .step choices148 bits1180 plan2938

def plan4546 : Plan := .step choices148 bits1184 plan2939

def plan4547 : Plan := .step choices148 bits1179 plan2940

def plan4548 : Plan := .step choices148 bits1182 plan2941

def plan4549 : Plan := .step choices148 bits1180 plan2942

def plan4550 : Plan := .step choices148 bits1183 plan2943

def plan4551 : Plan := .step choices148 bits1185 plan2944

def plan4552 : Plan := .step choices148 bits1183 plan2945

def plan4553 : Plan := .step choices148 bits1187 plan2946

def plan4554 : Plan := .step choices148 bits1185 plan2947

def plan4555 : Plan := .step choices148 bits1183 plan2948

def plan4556 : Plan := .step choices148 bits1188 plan2949

def plan4557 : Plan := .step choices148 bits1179 plan2951

def plan4558 : Plan := .step choices148 bits1181 plan2952

def plan4559 : Plan := .step choices148 bits1179 plan2953

def plan4560 : Plan := .step choices148 bits1180 plan2957

def plan4561 : Plan := .step choices148 bits1182 plan2958

def plan4562 : Plan := .step choices148 bits1180 plan2959

def plan4563 : Plan := .step choices148 bits1184 plan2960

def plan4564 : Plan := .step choices148 bits1179 plan2961

def plan4565 : Plan := .step choices148 bits1182 plan2962

def plan4566 : Plan := .step choices148 bits1180 plan2963

def plan4567 : Plan := .step choices148 bits1187 plan2964

def plan4568 : Plan := .step choices148 bits1185 plan2965

def plan4569 : Plan := .step choices148 bits1183 plan2966

def plan4570 : Plan := .step choices148 bits1180 plan2978

def plan4571 : Plan := .step choices148 bits1182 plan2979

def plan4572 : Plan := .step choices148 bits1180 plan2981

def plan4573 : Plan := .step choices148 bits1183 plan2982

def plan4574 : Plan := .step choices148 bits1185 plan2983

def plan4575 : Plan := .step choices148 bits1183 plan2984

def plan4576 : Plan := .step choices148 bits1187 plan2985

def plan4577 : Plan := .step choices148 bits1180 plan2987

def plan4578 : Plan := .step choices148 bits1182 plan2988

def plan4579 : Plan := .step choices148 bits1180 plan2990

def plan4580 : Plan := .step choices148 bits1185 plan2991

def plan4581 : Plan := .step choices148 bits1183 plan2992

def plan4582 : Plan := .step choices148 bits1186 plan2993

def plan4583 : Plan := .step choices148 bits1189 plan2994

def plan4584 : Plan := .step choices148 bits1186 plan2995

def plan4585 : Plan := .step choices148 bits1191 plan2996

def plan4586 : Plan := .step choices148 bits1189 plan2997

def plan4587 : Plan := .step choices148 bits1186 plan2998

def plan4588 : Plan := .step choices148 bits1192 plan2999

def plan4589 : Plan := .step choices148 bits1183 plan3003

def plan4590 : Plan := .step choices148 bits1185 plan3004

def plan4591 : Plan := .step choices148 bits1183 plan3005

def plan4592 : Plan := .step choices148 bits1187 plan3006

def plan4593 : Plan := .step choices148 bits1180 plan3008

def plan4594 : Plan := .step choices148 bits1182 plan3009

def plan4595 : Plan := .step choices148 bits1180 plan3011

def plan4596 : Plan := .step choices148 bits1185 plan3012

def plan4597 : Plan := .step choices148 bits1183 plan3013

def plan4598 : Plan := .step choices148 bits1191 plan3014

def plan4599 : Plan := .step choices148 bits1189 plan3015

def plan4600 : Plan := .step choices148 bits1186 plan3016

def plan4601 : Plan := .step choices148 bits1190 plan3017

def plan4602 : Plan := .step choices148 bits1193 plan3018

def plan4603 : Plan := .step choices148 bits1190 plan3019

def plan4604 : Plan := .step choices148 bits1194 plan3020

def plan4605 : Plan := .step choices148 bits1193 plan3021

def plan4606 : Plan := .step choices148 bits1190 plan3022

def plan4607 : Plan := .step choices148 bits1195 plan3023

def plan4608 : Plan := .step choices148 bits1194 plan3024

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


