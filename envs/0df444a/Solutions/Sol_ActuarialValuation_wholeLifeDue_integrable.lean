-- Prove2me | solution 1 for ActuarialValuation.wholeLifeDue_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:43:29.669398+00:00
-- url     : https://prove2.me/submissions/c86d1cb4-9b69-4fed-b441-40bea207a533

import Mathlib
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV

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
    Integrable (wholeLifeAnnuityDuePV K v) P := by
  have hv : v ≠ 1 := ne_of_lt hv1
  have hden : 0 < 1 - v := sub_pos.mpr hv1
  have hmeas : Measurable (wholeLifeAnnuityDuePV K v) := by
    have hdiscrete : Measurable (fun m : ℕ =>
        ∑ k ∈ Finset.range (m + 1), v ^ k) :=
      measurable_of_countable _
    change Measurable (fun ω => ∑ k ∈ Finset.range (K ω + 1), v ^ k)
    exact hdiscrete.comp hK
  have hgeom (m : ℕ) :
      (∑ k ∈ Finset.range m, v ^ k) = (1 - v ^ m) / (1 - v) := by
    rw [geom_sum_eq hv]
    have hneg : v - 1 = -(1 - v) := by ring
    rw [hneg]
    simp only [div_neg, neg_div]
    ring
  have hbound : ∀ ω, ‖wholeLifeAnnuityDuePV K v ω‖ ≤ 1 / (1 - v) := by
    intro ω
    have hpositive : 0 ≤ wholeLifeAnnuityDuePV K v ω := by
      unfold wholeLifeAnnuityDuePV
      apply Finset.sum_nonneg
      intro k hk
      exact pow_nonneg hv0 k
    have hpow : 0 ≤ v ^ (K ω + 1) := pow_nonneg hv0 _
    have hnum : 1 - v ^ (K ω + 1) ≤ 1 := by linarith
    have hratio :
        (1 - v ^ (K ω + 1)) / (1 - v) ≤ 1 / (1 - v) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    rw [Real.norm_eq_abs, abs_of_nonneg hpositive]
    change (∑ k ∈ Finset.range (K ω + 1), v ^ k) ≤ 1 / (1 - v)
    rw [hgeom]
    exact hratio
  exact Integrable.of_bound hmeas.aestronglyMeasurable
    (1 / (1 - v)) (Filter.Eventually.of_forall hbound)