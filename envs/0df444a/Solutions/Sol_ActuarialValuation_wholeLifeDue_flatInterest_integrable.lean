-- Prove2me | solution 1 for ActuarialValuation.wholeLifeDue_flatInterest_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:05:10.474064+00:00
-- url     : https://prove2.me/submissions/af8d154a-0047-41ec-8390-791fe2519fd7

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
    Integrable (wholeLifeAnnuityDuePV K (1 / (1 + i))) P := by
  have h1i_pos : 0 < 1 + i := by linarith
  have hi_ne : i ≠ 0 := ne_of_gt hi
  have h1i_ne : (1 : ℝ) + i ≠ 0 := ne_of_gt h1i_pos
  have hv0 : 0 ≤ 1 / (1 + i) := by positivity
  have hc_nonneg : 0 ≤ ((1 + i) / i : ℝ) :=
    div_nonneg (le_of_lt h1i_pos) (le_of_lt hi)
  have h1mv : 1 - 1 / (1 + i) = i / (1 + i) := by
    field_simp
    ring
  have hc_inv : ((1 : ℝ) + i) / i * (1 - 1 / (1 + i)) = 1 := by
    rw [h1mv]
    field_simp
  have hgeom : ∀ n : ℕ, (∑ k ∈ Finset.range n, (1 / (1 + i)) ^ k)
      = ((1 + i) / i) * (1 - (1 / (1 + i)) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      linear_combination -((1 / (1 + i)) ^ n) * hc_inv
  have hmeas : Measurable (wholeLifeAnnuityDuePV K (1 / (1 + i))) := by
    have hdis : Measurable
        (fun m : ℕ => ∑ k ∈ Finset.range (m + 1), (1 / (1 + i)) ^ k) :=
      measurable_of_countable _
    have hfun : Measurable
        (fun ω : Ω => ∑ k ∈ Finset.range (K ω + 1), (1 / (1 + i)) ^ k) := by
      simpa only [Function.comp_def] using hdis.comp hK
    have heq : (wholeLifeAnnuityDuePV K (1 / (1 + i)))
        = (fun ω : Ω => ∑ k ∈ Finset.range (K ω + 1), (1 / (1 + i)) ^ k) := by
      funext ω
      rfl
    rw [heq]
    exact hfun
  have hpoint : ∀ ω, wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
      = ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω) := by
    intro ω
    have h1 : wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
        = ∑ k ∈ Finset.range (K ω + 1), (1 / (1 + i)) ^ k := rfl
    have h2 : wholeLifeAssurancePV K (1 / (1 + i)) ω
        = (1 / (1 + i)) ^ (K ω + 1) := rfl
    rw [h1, h2]
    exact hgeom (K ω + 1)
  have hbound : ∀ ω, ‖wholeLifeAnnuityDuePV K (1 / (1 + i)) ω‖
      ≤ (1 + i) / i := by
    intro ω
    have hpos : 0 ≤ wholeLifeAnnuityDuePV K (1 / (1 + i)) ω := by
      have h1 : wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
          = ∑ k ∈ Finset.range (K ω + 1), (1 / (1 + i)) ^ k := rfl
      rw [h1]
      apply Finset.sum_nonneg
      intro k _
      exact pow_nonneg hv0 k
    have hnn : 0 ≤ (1 / (1 + i)) ^ (K ω + 1) := pow_nonneg hv0 _
    rw [Real.norm_eq_abs, abs_of_nonneg hpos, hpoint ω]
    have hle : (1 : ℝ) - wholeLifeAssurancePV K (1 / (1 + i)) ω ≤ 1 := by
      have h2 : wholeLifeAssurancePV K (1 / (1 + i)) ω
          = (1 / (1 + i)) ^ (K ω + 1) := rfl
      linarith
    calc ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω)
        ≤ ((1 + i) / i) * 1 := mul_le_mul_of_nonneg_left hle hc_nonneg
      _ = (1 + i) / i := mul_one _
  exact Integrable.of_bound hmeas.aestronglyMeasurable ((1 + i) / i)
    (Filter.Eventually.of_forall hbound)
