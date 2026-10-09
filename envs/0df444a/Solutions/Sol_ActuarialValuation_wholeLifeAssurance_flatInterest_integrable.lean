-- Prove2me | solution 1 for ActuarialValuation.wholeLifeAssurance_flatInterest_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:05:10.590075+00:00
-- url     : https://prove2.me/submissions/34f17d90-3621-4a65-9d1a-24245bcf1ab4

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (i : ℝ) (hi : 0 < i)
    :
    Integrable (wholeLifeAssurancePV K (1 / (1 + i))) P := by
  have h1i_pos : 0 < 1 + i := by linarith
  have hi_ne : i ≠ 0 := ne_of_gt hi
  have h1i_ne : (1 : ℝ) + i ≠ 0 := ne_of_gt h1i_pos
  have hv0 : 0 ≤ 1 / (1 + i) := by positivity
  have hv1 : 1 / (1 + i) < 1 := by
    rw [div_lt_one h1i_pos]
    linarith
  have hmeas : Measurable (wholeLifeAssurancePV K (1 / (1 + i))) := by
    have h1 : Measurable (fun n : ℕ => n + 1) := measurable_of_countable _
    have h2 : Measurable (fun n : ℕ => (1 / (1 + i)) ^ n) :=
      measurable_of_countable _
    have hfun : Measurable (fun ω : Ω => (1 / (1 + i)) ^ (K ω + 1)) := by
      simpa only [Function.comp_def] using h2.comp (h1.comp hK)
    have heq : (wholeLifeAssurancePV K (1 / (1 + i)))
        = (fun ω : Ω => (1 / (1 + i)) ^ (K ω + 1)) := by
      funext ω
      rfl
    rw [heq]
    exact hfun
  have hbound : ∀ ω, ‖wholeLifeAssurancePV K (1 / (1 + i)) ω‖ ≤ (1 : ℝ) := by
    intro ω
    have hle : (1 / (1 + i)) ^ (K ω + 1) ≤ 1 :=
      pow_le_one₀ hv0 (le_of_lt hv1)
    have hnn : 0 ≤ (1 / (1 + i)) ^ (K ω + 1) := pow_nonneg hv0 _
    have heq : wholeLifeAssurancePV K (1 / (1 + i)) ω
        = (1 / (1 + i)) ^ (K ω + 1) := rfl
    rw [heq, Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle
  exact Integrable.of_bound hmeas.aestronglyMeasurable 1
    (Filter.Eventually.of_forall hbound)
