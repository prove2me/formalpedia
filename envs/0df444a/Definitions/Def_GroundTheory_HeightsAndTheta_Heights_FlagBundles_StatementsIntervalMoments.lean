-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FlagBundles_StatementsIntervalMoments
-- name    : GroundTheory_HeightsAndTheta_Heights_FlagBundles_StatementsIntervalMoments
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:41.212146+00:00
-- url     : https://prove2.me/theorems/4927af78-4ed3-4460-b365-bea9c1b7cd0d
-- title:
--   Statements Interval Moments
-- statement:
--   Definitions and structural lemmas for Statements Interval Moments, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FlagBundles/StatementsIntervalMoments.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FlagBundles
open MeasureTheory
noncomputable section
def IntervalMomentsDetermine.Statement : Prop :=
  ∀ μ ν : Measure ℝ, IsFiniteMeasure μ → IsFiniteMeasure ν →
    μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0 →
    (∀ k : ℕ, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν) → μ = ν
example : IsFiniteMeasure (Measure.dirac (0 : ℝ)) ∧ Measure.dirac (0 : ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 ∧
    IsFiniteMeasure ((2⁻¹ : ENNReal) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)) ∧
    ((2⁻¹ : ENNReal) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.dirac_apply' _ (measurableSet_Icc.compl)]
    simp
  · exact ⟨by simp [ENNReal.mul_lt_top]⟩
  · simp [Measure.restrict_apply measurableSet_Icc.compl]
end
end GroundTheory.Heights₂.Heights.FlagBundles


