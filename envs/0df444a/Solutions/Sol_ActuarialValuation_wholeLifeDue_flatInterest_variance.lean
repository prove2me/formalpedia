-- Prove2me | solution 1 for ActuarialValuation.wholeLifeDue_flatInterest_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:06:41.321375+00:00
-- url     : https://prove2.me/submissions/81970ef4-b256-4f20-abf3-492a22268ced

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
    ProbabilityTheory.variance
      (wholeLifeAnnuityDuePV K (1 / (1 + i))) P =
      (((1 + i) / i) ^ 2) * ProbabilityTheory.variance
      (wholeLifeAssurancePV K (1 / (1 + i))) P := by
  have h1i_pos : 0 < 1 + i := by linarith
  have hi_ne : i ≠ 0 := ne_of_gt hi
  have h1i_ne : (1 : ℝ) + i ≠ 0 := ne_of_gt h1i_pos
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
  have hpoint : ∀ ω, wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
      = ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω) := by
    intro ω
    have h1 : wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
        = ∑ k ∈ Finset.range (K ω + 1), (1 / (1 + i)) ^ k := rfl
    have h2 : wholeLifeAssurancePV K (1 / (1 + i)) ω
        = (1 / (1 + i)) ^ (K ω + 1) := rfl
    rw [h1, h2]
    exact hgeom (K ω + 1)
  have hAss_meas : Measurable (wholeLifeAssurancePV K (1 / (1 + i))) := by
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
  have hfun_eq : wholeLifeAnnuityDuePV K (1 / (1 + i))
      = fun ω => ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω) := by
    funext ω
    exact hpoint ω
  rw [hfun_eq, ProbabilityTheory.variance_const_mul,
    ProbabilityTheory.variance_const_sub hAss_meas.aestronglyMeasurable]
