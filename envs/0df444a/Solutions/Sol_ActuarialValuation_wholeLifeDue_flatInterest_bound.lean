-- Prove2me | solution 1 for ActuarialValuation.wholeLifeDue_flatInterest_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:03:50.73755+00:00
-- url     : https://prove2.me/submissions/3d87017e-0018-4a9a-a4bd-4783ee26d97e

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (i : ℝ) (hi : 0 < i) (ω : Ω)
    :
    0 ≤ wholeLifeAnnuityDuePV K (1 / (1 + i)) ω ∧
      wholeLifeAnnuityDuePV K (1 / (1 + i)) ω ≤ (1 + i) / i := by
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
  have hpoint : wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
      = ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω) := by
    have h1 : wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
        = ∑ k ∈ Finset.range (K ω + 1), (1 / (1 + i)) ^ k := rfl
    have h2 : wholeLifeAssurancePV K (1 / (1 + i)) ω
        = (1 / (1 + i)) ^ (K ω + 1) := rfl
    rw [h1, h2]
    exact hgeom (K ω + 1)
  have hZnn : 0 ≤ wholeLifeAssurancePV K (1 / (1 + i)) ω := by
    have h2 : wholeLifeAssurancePV K (1 / (1 + i)) ω
        = (1 / (1 + i)) ^ (K ω + 1) := rfl
    rw [h2]
    exact pow_nonneg hv0 _
  constructor
  · have h1 : wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
        = ∑ k ∈ Finset.range (K ω + 1), (1 / (1 + i)) ^ k := rfl
    rw [h1]
    apply Finset.sum_nonneg
    intro k _
    exact pow_nonneg hv0 k
  · rw [hpoint]
    have hle : (1 : ℝ) - wholeLifeAssurancePV K (1 / (1 + i)) ω ≤ 1 := by
      linarith
    calc ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω)
        ≤ ((1 + i) / i) * 1 := mul_le_mul_of_nonneg_left hle hc_nonneg
      _ = (1 + i) / i := mul_one _
