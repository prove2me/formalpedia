-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans044
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans044
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:16.173719+00:00
-- url     : https://prove2.me/theorems/ade17aed-6188-4a88-9d38-090bec2ad9b2
-- title:
--   Endpoint22 Reach Plans044 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans044 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4293`, `ThreeBoundEndpoint22Reachable.plan4294`, `ThreeBoundEndpoint22Reachable.plan4295`, `ThreeBoundEndpoint22Reachable.plan4296`, `ThreeBoundEndpoint22Reachable.plan4297`, `ThreeBoundEndpoint22Reachable.plan4298`, `ThreeBoundEndpoint22Reachable.plan4299`, `ThreeBoundEndpoint22Reachable.plan4230`, `ThreeBoundEndpoint22Reachable.plan4300`, `ThreeBoundEndpoint22Reachable.plan4301`, `ThreeBoundEndpoint22Reachable.plan4302`, `ThreeBoundEndpoint22Reachable.plan4303`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans044.lean, lines 1–205.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits007
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits008
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans028
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans029
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
def plan4225 : Plan := .step choices137 bits1029 plan2863

def plan4226 : Plan := .step choices137 bits1028 plan2864

def plan4227 : Plan := .step choices137 bits1030 plan2865

def plan4228 : Plan := .step choices137 bits1029 plan2866

def plan4229 : Plan := .step choices137 bits1028 plan2867

def plan4230 : Plan := .step choices137 bits1024 plan2869

def plan4231 : Plan := .step choices137 bits1028 plan2870

def plan4232 : Plan := .step choices137 bits1024 plan2871

def plan4233 : Plan := .step choices137 bits1020 plan2872

def plan4234 : Plan := .step choices138 bits1020 plan2722

def plan4235 : Plan := .step choices138 bits1024 plan2723

def plan4236 : Plan := .step choices138 bits1028 plan2724

def plan4237 : Plan := .step choices138 bits1020 plan2725

def plan4238 : Plan := .step choices138 bits1024 plan2726

def plan4239 : Plan := .step choices138 bits1028 plan2727

def plan4240 : Plan := .step choices138 bits1029 plan2728

def plan4241 : Plan := .step choices138 bits1028 plan2729

def plan4242 : Plan := .step choices138 bits1030 plan2730

def plan4243 : Plan := .step choices138 bits1024 plan2732

def plan4244 : Plan := .step choices138 bits1028 plan2733

def plan4245 : Plan := .step choices138 bits1020 plan2734

def plan4246 : Plan := .step choices138 bits1024 plan2735

def plan4247 : Plan := .step choices138 bits1029 plan2736

def plan4248 : Plan := .step choices138 bits1028 plan2737

def plan4249 : Plan := .step choices138 bits1029 plan2738

def plan4250 : Plan := .step choices138 bits1030 plan2739

def plan4251 : Plan := .step choices138 bits1029 plan2740

def plan4252 : Plan := .step choices138 bits1031 plan2741

def plan4253 : Plan := .step choices138 bits1030 plan2742

def plan4254 : Plan := .step choices138 bits1029 plan2743

def plan4255 : Plan := .step choices138 bits1032 plan2744

def plan4256 : Plan := .step choices138 bits1028 plan2748

def plan4257 : Plan := .step choices138 bits1029 plan2749

def plan4258 : Plan := .step choices138 bits1028 plan2750

def plan4259 : Plan := .step choices138 bits1030 plan2751

def plan4260 : Plan := .step choices138 bits1024 plan2753

def plan4261 : Plan := .step choices138 bits1028 plan2754

def plan4262 : Plan := .step choices138 bits1020 plan2755

def plan4263 : Plan := .step choices138 bits1024 plan2756

def plan4264 : Plan := .step choices138 bits1029 plan2757

def plan4265 : Plan := .step choices138 bits1028 plan2758

def plan4266 : Plan := .step choices138 bits1031 plan2759

def plan4267 : Plan := .step choices138 bits1030 plan2760

def plan4268 : Plan := .step choices138 bits1029 plan2761

def plan4269 : Plan := .step choices138 bits1041 plan2768

def plan4270 : Plan := .step choices138 bits1042 plan2769

def plan4271 : Plan := .step choices138 bits1041 plan2770

def plan4272 : Plan := .step choices138 bits1043 plan2771

def plan4273 : Plan := .step choices138 bits1042 plan2772

def plan4274 : Plan := .step choices138 bits1041 plan2773

def plan4275 : Plan := .step choices138 bits1044 plan2774

def plan4276 : Plan := .step choices138 bits1043 plan2775

def plan4277 : Plan := .step choices138 bits1042 plan2776

def plan4278 : Plan := .step choices138 bits1041 plan2777

def plan4279 : Plan := .step choices138 bits1040 plan2812

def plan4280 : Plan := .step choices138 bits1041 plan2813

def plan4281 : Plan := .step choices138 bits1040 plan2814

def plan4282 : Plan := .step choices138 bits1042 plan2815

def plan4283 : Plan := .step choices138 bits1041 plan2816

def plan4284 : Plan := .step choices138 bits1040 plan2817

def plan4285 : Plan := .step choices138 bits1039 plan2819

def plan4286 : Plan := .step choices138 bits1040 plan2820

def plan4287 : Plan := .step choices138 bits1039 plan2821

def plan4288 : Plan := .step choices138 bits1034 plan2822

def plan4289 : Plan := .step choices138 bits1034 plan2823

def plan4290 : Plan := .step choices138 bits1039 plan2825

def plan4291 : Plan := .step choices138 bits1040 plan2826

def plan4292 : Plan := .step choices138 bits1039 plan2827

def plan4293 : Plan := .step choices138 bits1034 plan2828

def plan4294 : Plan := .step choices138 bits1040 plan2862

def plan4295 : Plan := .step choices138 bits1041 plan2863

def plan4296 : Plan := .step choices138 bits1040 plan2864

def plan4297 : Plan := .step choices138 bits1042 plan2865

def plan4298 : Plan := .step choices138 bits1041 plan2866

def plan4299 : Plan := .step choices138 bits1040 plan2867

def plan4300 : Plan := .step choices138 bits1039 plan2869

def plan4301 : Plan := .step choices138 bits1040 plan2870

def plan4302 : Plan := .step choices138 bits1039 plan2871

def plan4303 : Plan := .step choices138 bits1034 plan2872

def plan4304 : Plan := .step choices139 bits1048 plan2768

def plan4305 : Plan := .step choices139 bits1049 plan2769

def plan4306 : Plan := .step choices139 bits1048 plan2770

def plan4307 : Plan := .step choices139 bits1050 plan2771

def plan4308 : Plan := .step choices139 bits1049 plan2772

def plan4309 : Plan := .step choices139 bits1048 plan2773

def plan4310 : Plan := .step choices139 bits1051 plan2774

def plan4311 : Plan := .step choices139 bits1050 plan2775

def plan4312 : Plan := .step choices139 bits1049 plan2776

def plan4313 : Plan := .step choices139 bits1048 plan2777

def plan4314 : Plan := .step choices140 bits1008 plan2700

def plan4315 : Plan := .step choices140 bits1010 plan2701

def plan4316 : Plan := .step choices140 bits1008 plan2702

def plan4317 : Plan := .step choices140 bits1010 plan2703

def plan4318 : Plan := .step choices140 bits1011 plan2704

def plan4319 : Plan := .step choices140 bits1010 plan2705

def plan4320 : Plan := .step choices140 bits1012 plan2706

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


