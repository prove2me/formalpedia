-- Prove2me | Definitions.Def_SourceProof_00b40815a5461bbd48826370
-- name    : SourceProof_00b40815a5461bbd48826370
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:06:18.001468+00:00
-- url     : https://prove2.me/theorems/0a939a9a-ccf2-43f1-a8fb-7b8b209dcad1
-- title:
--   LevyStochCalc source proof: InnerProductSpace.volume_closedBall_div'
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_MeasureTheory_F000


/-!
# Measure theory lemmas to be upstreamed to Mathlib
-/

@[expose] public section

open MeasureTheory WithLp

open scoped ENNReal NNReal ProbabilityTheory

                                     

namespace ProbabilityTheory

section iIndepFun

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable [∀ i, IsProbabilityMeasure (μ i)]

end iIndepFun

section covariance

end covariance

end ProbabilityTheory

--generalizing `MeasureTheory.Measure.addHaar_ball_center`

open Metric

theorem _root_.Prove2MeSourceProof.h_00b40815a5461bbd48826370 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (x y : E) (r s : ℝ≥0∞) :
    volume (Metric.closedEBall x r) / volume (Metric.closedEBall y s) =
      (r / s) ^ (Module.finrank ℝ E) := by
  nontriviality E
  obtain rfl | hr := eq_top_or_lt_top r <;> obtain rfl | hs := eq_top_or_lt_top s
  · simp
  · lift s to ℝ≥0 using hs.ne
    simp [ENNReal.top_div, closedEBall_coe, (isCompact_closedBall _ _).measure_ne_top]
  · simp
  · obtain rfl | hr' := eq_zero_or_pos r <;> obtain rfl | hs' := eq_zero_or_pos s
    · simp
    · simp
    · simp [ENNReal.div_zero, hr'.ne', Metric.measure_closedEBall_pos volume x hr'.ne' |>.ne']
    lift r to ℝ≥0 using hr.ne
    lift s to ℝ≥0 using hs.ne
    simp_rw [closedEBall_coe]
    rw [InnerProductSpace.volume_closedBall_div, ENNReal.ofReal_div_of_pos]
    · simp
    all_goals simp_all
section covariance

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y Z : Ω → ℝ} (c : ℝ)

end ProbabilityTheory

open ProbabilityTheory MeasurableSpace

end covariance


