-- Prove2me | solution 1 for ActuarialValuation.wholeLifeYearInnovation_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:47:56.825699+00:00
-- url     : https://prove2.me/submissions/5e9b699c-75b0-4162-93bb-c877f8599067

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (t : ℕ)
  (hw : Summable w) (hS : 0 < wholeLifeTailMass w t) :
  (∑' k : ℕ, w k * wholeLifeYearInnovation w t k) = 0 := by
  let c : ℝ := w t / wholeLifeTailMass w t
  have hsingle : Summable (fun k : ℕ => if k = t then w k else 0) := by
    apply (hw.norm).of_norm_bounded
    intro k
    split_ifs <;> simp [Real.norm_eq_abs]
  have htail : Summable (fun k : ℕ => if t ≤ k then w k else 0) := by
    apply (hw.norm).of_norm_bounded
    intro k
    split_ifs <;> simp [Real.norm_eq_abs]
  have hctail : Summable (fun k : ℕ => c * (if t ≤ k then w k else 0)) :=
    htail.mul_left c
  have hpoint (k : ℕ) :
      w k * wholeLifeYearInnovation w t k =
        (if k = t then w k else 0) -
          c * (if t ≤ k then w k else 0) := by
    simp [wholeLifeYearInnovation, c, mul_sub, mul_ite, mul_assoc]
    split_ifs <;> ring
  calc
    (∑' k : ℕ, w k * wholeLifeYearInnovation w t k) =
        ∑' k : ℕ, ((if k = t then w k else 0) -
          c * (if t ≤ k then w k else 0)) := by
          apply tsum_congr
          intro k
          exact hpoint k
    _ = (∑' k : ℕ, if k = t then w k else 0) -
        c * (∑' k : ℕ, if t ≤ k then w k else 0) := by
          rw [hsingle.tsum_sub hctail, tsum_mul_left]
    _ = w t - c * wholeLifeTailMass w t := by
          simp [wholeLifeTailMass] <;> ring
    _ = 0 := by
          dsimp [c]
          field_simp [ne_of_gt hS] <;> ring
