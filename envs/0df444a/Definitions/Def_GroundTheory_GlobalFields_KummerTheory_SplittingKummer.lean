-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingKummer
-- name    : GroundTheory_GlobalFields_KummerTheory_SplittingKummer
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:49.987592+00:00
-- url     : https://prove2.me/theorems/de220334-48a4-4ad2-8150-890df93d8225
-- title:
--   Splitting Kummer
-- statement:
--   Definitions and structural lemmas for Splitting Kummer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingKummer.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Global
open IsDedekindDomain NumberField Module IntermediateField GroundTheory.ProfCoh
open scoped TensorProduct
section Local
variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] {Δ : Subgroup Kˣ}
  {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]
end Local
section Global
variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω] {Δ : Subgroup Kˣ}
  [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]
instance numberField_kummerExtension : NumberField (kummerExtension K n Ω Δ) :=
  NumberField.of_module_finite K _
end Global
end GroundTheory.Global


