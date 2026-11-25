-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroForallNormLeOfCovolumeLe
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroForallNormLeOfCovolumeLe
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:09:35.894458+00:00
-- url     : https://prove2.me/theorems/0fb68776-97b0-5696-bea1-8d4f5be93298
-- title:
--   Exists Ne Zero Forall Norm Le Of Covolume Le
-- statement:
--   Definitions and structural lemmas for Exists Ne Zero Forall Norm Le Of Covolume Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroForallNormLeOfCovolumeLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module MeasureTheory Metric Set
open scoped Real ENNReal
namespace GlobalTheory
section Lattice
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
end Lattice
section Strip
def shearedBox (M ρ y : ℝ) : Set ℂ := {z | |2 * z.re| ≤ M ∧ |2 * z.re * y - z.im| ≤ ρ}
end Strip
section TotallyComplex
open InfinitePlace
end TotallyComplex
section CM
open InfinitePlace IsCMField
open scoped nonZeroDivisors
variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
end CM
section Constant
end Constant
section Balls
variable {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℝ (W i)] [∀ i, FiniteDimensional ℝ (W i)]
  [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end Balls
end GlobalTheory


