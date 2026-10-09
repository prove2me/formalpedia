-- Prove2me | solution 1 for ActuarialValuation.flatInterest_geometric_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:03:51.946826+00:00
-- url     : https://prove2.me/submissions/f8b16a96-9676-4809-9271-9e04c3943d41

import Mathlib
import Definitions.Def_actuarial_wholeLifeAnnuityDuePV
import Definitions.Def_actuarial_wholeLifeAssurancePV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution (i : ℝ) (hi : 0 < i) (m : ℕ)
    :
    (∑ k ∈ Finset.range (m + 1), (1 / (1 + i) : ℝ) ^ k) =
      ((1 + i) / i) * (1 - (1 / (1 + i) : ℝ) ^ (m + 1)) := by
  have h1i_pos : 0 < 1 + i := by linarith
  have hi_ne : i ≠ 0 := ne_of_gt hi
  have h1i_ne : (1 : ℝ) + i ≠ 0 := ne_of_gt h1i_pos
  have h1mv : 1 - 1 / (1 + i) = i / (1 + i) := by
    field_simp
    ring
  have hc_inv : ((1 : ℝ) + i) / i * (1 - 1 / (1 + i)) = 1 := by
    rw [h1mv]
    field_simp
  induction m with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, pow_one]
    exact hc_inv.symm
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    linear_combination -((1 / (1 + i)) ^ (m + 1)) * hc_inv
