-- Prove2me | solution 1 for ActuarialValuation.wholeLifeImmediate_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:43:33.639683+00:00
-- url     : https://prove2.me/submissions/84c6be35-049d-45a4-98c7-e185b03ab196

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAnnuityImmediatePV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    :
    Integrable (wholeLifeAnnuityImmediatePV K v) P := by
  have hv : v ≠ 1 := ne_of_lt hv1
  have hden : 0 < 1 - v := sub_pos.mpr hv1
  have hmeas : Measurable (wholeLifeAnnuityImmediatePV K v) := by
    have hdiscrete : Measurable (fun m : ℕ =>
        ∑ k ∈ Finset.range m, v ^ (k + 1)) :=
      measurable_of_countable _
    change Measurable (fun ω => ∑ k ∈ Finset.range (K ω), v ^ (k + 1))
    exact hdiscrete.comp hK
  have hgeom (m : ℕ) :
      (∑ k ∈ Finset.range m, v ^ k) = (1 - v ^ m) / (1 - v) := by
    rw [geom_sum_eq hv]
    have hneg : v - 1 = -(1 - v) := by ring
    rw [hneg]
    simp only [div_neg, neg_div]
    ring
  have hfirst (ω : Ω) :
      wholeLifeAnnuityImmediatePV K v ω =
        wholeLifeAnnuityDuePV K v ω - 1 := by
    unfold wholeLifeAnnuityDuePV wholeLifeAnnuityImmediatePV
    rw [Finset.sum_range_succ']
    simp only [pow_zero]
    ring
  have hbound : ∀ ω, ‖wholeLifeAnnuityImmediatePV K v ω‖ ≤ 1 / (1 - v) := by
    intro ω
    have hpositive : 0 ≤ wholeLifeAnnuityImmediatePV K v ω := by
      unfold wholeLifeAnnuityImmediatePV
      apply Finset.sum_nonneg
      intro k hk
      exact pow_nonneg hv0 (k + 1)
    have hpow : 0 ≤ v ^ (K ω + 1) := pow_nonneg hv0 _
    have hnum : 1 - v ^ (K ω + 1) ≤ 1 := by linarith
    have hratio :
        (1 - v ^ (K ω + 1)) / (1 - v) ≤ 1 / (1 - v) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    have hdue : wholeLifeAnnuityDuePV K v ω ≤ 1 / (1 - v) := by
      unfold wholeLifeAnnuityDuePV
      rw [hgeom]
      exact hratio
    rw [Real.norm_eq_abs, abs_of_nonneg hpositive, hfirst]
    linarith
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (1 / (1 - v)) (Filter.Eventually.of_forall hbound)