-- Prove2me | solution 1 for ActuarialValuation.tailRiskSelectedLoss_stoploss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:43:03.748239+00:00
-- url     : https://prove2.me/submissions/25906d37-8a8e-4f39-99d2-8680300752b4

import Mathlib
import Definitions.Def_actuarial_tailRiskSelectedLoss
import Definitions.Def_actuarial_tailRiskStopLoss
import Definitions.Def_actuarial_tailRiskStrictMass
import Definitions.Def_actuarial_tailRiskAtomWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ) :
  tailRiskSelectedLoss w bound q alpha =
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
