-- Prove2me | solution 1 for ActuarialValuation.tailRiskTVaR_stoploss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:49:53.862522+00:00
-- url     : https://prove2.me/submissions/06fdee20-ca73-453c-b0e6-57d59d09ad7e

import Mathlib
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskSelectedLoss
import Definitions.Def_actuarial_tailRiskStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (ha : alpha < 1) :
  tailRiskTVaR w bound q alpha =
    (q : ℝ) + tailRiskStopLoss w bound q / (1 - alpha) := by
  have hsel : tailRiskSelectedLoss w bound q alpha =
      (q : ℝ) * (1 - alpha) + tailRiskStopLoss w bound q := by
    have key :
        (∑ s ∈ Finset.range (bound + 1),
          if q < s then (s : ℝ) * w s else 0) =
        tailRiskStopLoss w bound q +
          (q : ℝ) * tailRiskStrictMass w bound q := by
      unfold tailRiskStopLoss tailRiskStrictMass
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases h : q < s
      · simp only [if_pos h]
        have hnat : s - q + q = s :=
          Nat.sub_add_cancel (Nat.le_of_lt h)
        have hr : ((s - q : ℕ) : ℝ) + (q : ℝ) = (s : ℝ) := by
          exact_mod_cast hnat
        calc
          (s : ℝ) * w s =
              (((s - q : ℕ) : ℝ) + (q : ℝ)) * w s := by rw [hr]
          _ = ((s - q : ℕ) : ℝ) * w s + (q : ℝ) * w s := by ring
      · have hle : s ≤ q := le_of_not_gt h
        simp [h, Nat.sub_eq_zero_of_le hle]
    unfold tailRiskSelectedLoss tailRiskAtomWeight
    rw [key]
    ring
  have hden : 1 - alpha ≠ 0 := by linarith
  unfold tailRiskTVaR
  rw [hsel]
  field_simp [hden]
