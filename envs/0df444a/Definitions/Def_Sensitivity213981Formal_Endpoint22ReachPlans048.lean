-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans048
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans048
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:36.292041+00:00
-- url     : https://prove2.me/theorems/b2f30af6-8489-4879-a48f-8f72810b3bb6
-- title:
--   Endpoint22 Reach Plans048 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans048 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4677`, `ThreeBoundEndpoint22Reachable.plan4678`, `ThreeBoundEndpoint22Reachable.plan4679`, `ThreeBoundEndpoint22Reachable.plan4680`, `ThreeBoundEndpoint22Reachable.plan4681`, `ThreeBoundEndpoint22Reachable.plan4682`, `ThreeBoundEndpoint22Reachable.plan4614`, `ThreeBoundEndpoint22Reachable.plan4683`, `ThreeBoundEndpoint22Reachable.plan4684`, `ThreeBoundEndpoint22Reachable.plan4685`, `ThreeBoundEndpoint22Reachable.plan4686`, `ThreeBoundEndpoint22Reachable.plan4687`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans048.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits009
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
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
def plan4609 : Plan := .step choices148 bits1193 plan3025

def plan4610 : Plan := .step choices148 bits1190 plan3026

def plan4611 : Plan := .step choices148 bits1196 plan3027

def plan4612 : Plan := .step choices148 bits1179 plan3045

def plan4613 : Plan := .step choices148 bits1180 plan3046

def plan4614 : Plan := .step choices148 bits1182 plan3047

def plan4615 : Plan := .step choices148 bits1180 plan3048

def plan4616 : Plan := .step choices148 bits1184 plan3049

def plan4617 : Plan := .step choices148 bits1179 plan3050

def plan4618 : Plan := .step choices148 bits1182 plan3051

def plan4619 : Plan := .step choices148 bits1180 plan3052

def plan4620 : Plan := .step choices148 bits1183 plan3053

def plan4621 : Plan := .step choices148 bits1185 plan3054

def plan4622 : Plan := .step choices148 bits1183 plan3055

def plan4623 : Plan := .step choices148 bits1187 plan3056

def plan4624 : Plan := .step choices148 bits1185 plan3057

def plan4625 : Plan := .step choices148 bits1183 plan3058

def plan4626 : Plan := .step choices148 bits1188 plan3059

def plan4627 : Plan := .step choices148 bits1179 plan3061

def plan4628 : Plan := .step choices148 bits1181 plan3062

def plan4629 : Plan := .step choices148 bits1179 plan3063

def plan4630 : Plan := .step choices148 bits1180 plan3067

def plan4631 : Plan := .step choices148 bits1182 plan3068

def plan4632 : Plan := .step choices148 bits1180 plan3069

def plan4633 : Plan := .step choices148 bits1184 plan3070

def plan4634 : Plan := .step choices148 bits1179 plan3071

def plan4635 : Plan := .step choices148 bits1182 plan3072

def plan4636 : Plan := .step choices148 bits1180 plan3073

def plan4637 : Plan := .step choices148 bits1187 plan3074

def plan4638 : Plan := .step choices148 bits1185 plan3075

def plan4639 : Plan := .step choices148 bits1183 plan3076

def plan4640 : Plan := .step choices148 bits1186 plan3083

def plan4641 : Plan := .step choices148 bits1189 plan3084

def plan4642 : Plan := .step choices148 bits1186 plan3085

def plan4643 : Plan := .step choices148 bits1191 plan3086

def plan4644 : Plan := .step choices148 bits1189 plan3087

def plan4645 : Plan := .step choices148 bits1186 plan3088

def plan4646 : Plan := .step choices148 bits1192 plan3089

def plan4647 : Plan := .step choices148 bits1183 plan3093

def plan4648 : Plan := .step choices148 bits1185 plan3094

def plan4649 : Plan := .step choices148 bits1183 plan3095

def plan4650 : Plan := .step choices148 bits1187 plan3096

def plan4651 : Plan := .step choices148 bits1180 plan3098

def plan4652 : Plan := .step choices148 bits1182 plan3099

def plan4653 : Plan := .step choices148 bits1180 plan3101

def plan4654 : Plan := .step choices148 bits1185 plan3102

def plan4655 : Plan := .step choices148 bits1183 plan3103

def plan4656 : Plan := .step choices148 bits1191 plan3104

def plan4657 : Plan := .step choices148 bits1189 plan3105

def plan4658 : Plan := .step choices148 bits1186 plan3106

def plan4659 : Plan := .step choices148 bits1195 plan3107

def plan4660 : Plan := .step choices148 bits1194 plan3108

def plan4661 : Plan := .step choices148 bits1193 plan3109

def plan4662 : Plan := .step choices148 bits1190 plan3110

def plan4663 : Plan := .step choices149 bits1198 plan2977

def plan4664 : Plan := .step choices149 bits1200 plan2978

def plan4665 : Plan := .step choices149 bits1202 plan2979

def plan4666 : Plan := .step choices149 bits1198 plan2980

def plan4667 : Plan := .step choices149 bits1200 plan2981

def plan4668 : Plan := .step choices149 bits1203 plan2982

def plan4669 : Plan := .step choices149 bits1205 plan2983

def plan4670 : Plan := .step choices149 bits1203 plan2984

def plan4671 : Plan := .step choices149 bits1207 plan2985

def plan4672 : Plan := .step choices149 bits1200 plan2987

def plan4673 : Plan := .step choices149 bits1202 plan2988

def plan4674 : Plan := .step choices149 bits1198 plan2989

def plan4675 : Plan := .step choices149 bits1200 plan2990

def plan4676 : Plan := .step choices149 bits1205 plan2991

def plan4677 : Plan := .step choices149 bits1203 plan2992

def plan4678 : Plan := .step choices149 bits1206 plan2993

def plan4679 : Plan := .step choices149 bits1209 plan2994

def plan4680 : Plan := .step choices149 bits1206 plan2995

def plan4681 : Plan := .step choices149 bits1211 plan2996

def plan4682 : Plan := .step choices149 bits1209 plan2997

def plan4683 : Plan := .step choices149 bits1206 plan2998

def plan4684 : Plan := .step choices149 bits1212 plan2999

def plan4685 : Plan := .step choices149 bits1203 plan3003

def plan4686 : Plan := .step choices149 bits1205 plan3004

def plan4687 : Plan := .step choices149 bits1203 plan3005

def plan4688 : Plan := .step choices149 bits1207 plan3006

def plan4689 : Plan := .step choices149 bits1200 plan3008

def plan4690 : Plan := .step choices149 bits1202 plan3009

def plan4691 : Plan := .step choices149 bits1198 plan3010

def plan4692 : Plan := .step choices149 bits1200 plan3011

def plan4693 : Plan := .step choices149 bits1205 plan3012

def plan4694 : Plan := .step choices149 bits1203 plan3013

def plan4695 : Plan := .step choices149 bits1211 plan3014

def plan4696 : Plan := .step choices149 bits1209 plan3015

def plan4697 : Plan := .step choices149 bits1206 plan3016

def plan4698 : Plan := .step choices149 bits1210 plan3017

def plan4699 : Plan := .step choices149 bits1213 plan3018

def plan4700 : Plan := .step choices149 bits1210 plan3019

def plan4701 : Plan := .step choices149 bits1214 plan3020

def plan4702 : Plan := .step choices149 bits1213 plan3021

def plan4703 : Plan := .step choices149 bits1210 plan3022

def plan4704 : Plan := .step choices149 bits1215 plan3023

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


