-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans045
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans045
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T22:49:19.780311+00:00
-- url     : https://prove2.me/theorems/0c9a09ff-876f-4d48-ba9a-63f78c23c853
-- title:
--   Endpoint22 Reach Plans045 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans045 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan4389`, `ThreeBoundEndpoint22Reachable.plan4390`, `ThreeBoundEndpoint22Reachable.plan4391`, `ThreeBoundEndpoint22Reachable.plan4392`, `ThreeBoundEndpoint22Reachable.plan4393`, `ThreeBoundEndpoint22Reachable.plan4394`, `ThreeBoundEndpoint22Reachable.plan4395`, `ThreeBoundEndpoint22Reachable.plan4326`, `ThreeBoundEndpoint22Reachable.plan4396`, `ThreeBoundEndpoint22Reachable.plan4397`, `ThreeBoundEndpoint22Reachable.plan4398`, `ThreeBoundEndpoint22Reachable.plan4399`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans045.lean, lines 1–205.

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
def plan4321 : Plan := .step choices140 bits1008 plan2707

def plan4322 : Plan := .step choices140 bits1010 plan2708

def plan4323 : Plan := .step choices140 bits1008 plan2709

def plan4324 : Plan := .step choices140 bits1011 plan2710

def plan4325 : Plan := .step choices140 bits1010 plan2711

def plan4326 : Plan := .step choices140 bits1025 plan2712

def plan4327 : Plan := .step choices140 bits1026 plan2713

def plan4328 : Plan := .step choices140 bits1025 plan2714

def plan4329 : Plan := .step choices140 bits1027 plan2715

def plan4330 : Plan := .step choices140 bits1026 plan2716

def plan4331 : Plan := .step choices140 bits1025 plan2717

def plan4332 : Plan := .step choices140 bits1023 plan2718

def plan4333 : Plan := .step choices140 bits1025 plan2719

def plan4334 : Plan := .step choices140 bits1023 plan2720

def plan4335 : Plan := .step choices140 bits1019 plan2721

def plan4336 : Plan := .step choices140 bits1019 plan2731

def plan4337 : Plan := .step choices140 bits1023 plan2745

def plan4338 : Plan := .step choices140 bits1025 plan2746

def plan4339 : Plan := .step choices140 bits1023 plan2747

def plan4340 : Plan := .step choices140 bits1019 plan2752

def plan4341 : Plan := .step choices140 bits1036 plan2762

def plan4342 : Plan := .step choices140 bits1037 plan2763

def plan4343 : Plan := .step choices140 bits1036 plan2764

def plan4344 : Plan := .step choices140 bits1038 plan2765

def plan4345 : Plan := .step choices140 bits1037 plan2766

def plan4346 : Plan := .step choices140 bits1036 plan2767

def plan4347 : Plan := .step choices140 bits997 plan2778

def plan4348 : Plan := .step choices140 bits1006 plan2779

def plan4349 : Plan := .step choices140 bits1007 plan2780

def plan4350 : Plan := .step choices140 bits1006 plan2781

def plan4351 : Plan := .step choices140 bits1021 plan2790

def plan4352 : Plan := .step choices140 bits1022 plan2791

def plan4353 : Plan := .step choices140 bits1021 plan2792

def plan4354 : Plan := .step choices140 bits1018 plan2800

def plan4355 : Plan := .step choices140 bits1018 plan2805

def plan4356 : Plan := .step choices140 bits1035 plan2809

def plan4357 : Plan := .step choices140 bits1036 plan2810

def plan4358 : Plan := .step choices140 bits1035 plan2811

def plan4359 : Plan := .step choices140 bits1033 plan2818

def plan4360 : Plan := .step choices140 bits1033 plan2824

def plan4361 : Plan := .step choices140 bits997 plan2829

def plan4362 : Plan := .step choices140 bits1006 plan2830

def plan4363 : Plan := .step choices140 bits1007 plan2831

def plan4364 : Plan := .step choices140 bits1006 plan2832

def plan4365 : Plan := .step choices140 bits1021 plan2841

def plan4366 : Plan := .step choices140 bits1022 plan2842

def plan4367 : Plan := .step choices140 bits1021 plan2843

def plan4368 : Plan := .step choices140 bits1018 plan2850

def plan4369 : Plan := .step choices140 bits1018 plan2855

def plan4370 : Plan := .step choices140 bits1035 plan2859

def plan4371 : Plan := .step choices140 bits1036 plan2860

def plan4372 : Plan := .step choices140 bits1035 plan2861

def plan4373 : Plan := .step choices140 bits1033 plan2868

def plan4374 : Plan := .step choices141 bits1047 plan2762

def plan4375 : Plan := .step choices141 bits1048 plan2763

def plan4376 : Plan := .step choices141 bits1047 plan2764

def plan4377 : Plan := .step choices141 bits1049 plan2765

def plan4378 : Plan := .step choices141 bits1048 plan2766

def plan4379 : Plan := .step choices141 bits1047 plan2767

def plan4380 : Plan := .step choices141 bits1046 plan2809

def plan4381 : Plan := .step choices141 bits1047 plan2810

def plan4382 : Plan := .step choices141 bits1046 plan2811

def plan4383 : Plan := .step choices141 bits1045 plan2818

def plan4384 : Plan := .step choices141 bits1045 plan2824

def plan4385 : Plan := .step choices141 bits1046 plan2859

def plan4386 : Plan := .step choices141 bits1047 plan2860

def plan4387 : Plan := .step choices141 bits1046 plan2861

def plan4388 : Plan := .step choices141 bits1045 plan2868

def plan4389 : Plan := .step choices144 bits1008 plan2700

def plan4390 : Plan := .step choices144 bits1010 plan2701

def plan4391 : Plan := .step choices144 bits1008 plan2702

def plan4392 : Plan := .step choices144 bits1010 plan2703

def plan4393 : Plan := .step choices144 bits1011 plan2704

def plan4394 : Plan := .step choices144 bits1010 plan2705

def plan4395 : Plan := .step choices144 bits1012 plan2706

def plan4396 : Plan := .step choices144 bits1008 plan2707

def plan4397 : Plan := .step choices144 bits1010 plan2708

def plan4398 : Plan := .step choices144 bits1008 plan2709

def plan4399 : Plan := .step choices144 bits1011 plan2710

def plan4400 : Plan := .step choices144 bits1010 plan2711

def plan4401 : Plan := .step choices144 bits1025 plan2712

def plan4402 : Plan := .step choices144 bits1026 plan2713

def plan4403 : Plan := .step choices144 bits1025 plan2714

def plan4404 : Plan := .step choices144 bits1027 plan2715

def plan4405 : Plan := .step choices144 bits1026 plan2716

def plan4406 : Plan := .step choices144 bits1025 plan2717

def plan4407 : Plan := .step choices144 bits1023 plan2718

def plan4408 : Plan := .step choices144 bits1025 plan2719

def plan4409 : Plan := .step choices144 bits1023 plan2720

def plan4410 : Plan := .step choices144 bits1019 plan2721

def plan4411 : Plan := .step choices144 bits1019 plan2731

def plan4412 : Plan := .step choices144 bits1023 plan2745

def plan4413 : Plan := .step choices144 bits1025 plan2746

def plan4414 : Plan := .step choices144 bits1023 plan2747

def plan4415 : Plan := .step choices144 bits1019 plan2752

def plan4416 : Plan := .step choices144 bits1036 plan2762

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


