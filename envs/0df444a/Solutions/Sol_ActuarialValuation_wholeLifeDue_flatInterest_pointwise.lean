-- Prove2me | solution 1 for ActuarialValuation.wholeLifeDue_flatInterest_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:03:52.334723+00:00
-- url     : https://prove2.me/submissions/50411ca2-e909-4397-b094-3df3ea4cfed2

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
    wholeLifeAnnuityDuePV K (1 / (1 + i)) ω =
      ((1 + i) / i) * (1 - wholeLifeAssurancePV K (1 / (1 + i)) ω) := by
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
  have h1 : wholeLifeAnnuityDuePV K (1 / (1 + i)) ω
      = ∑ k ∈ Finset.range (K ω + 1), (1 / (1 + i)) ^ k := rfl
  have h2 : wholeLifeAssurancePV K (1 / (1 + i)) ω
      = (1 / (1 + i)) ^ (K ω + 1) := rfl
  rw [h1, h2]
  exact hgeom (K ω + 1)
