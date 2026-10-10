-- Prove2me | solution 1 for ActuarialValuation.tailRiskTVaR_at_max
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:45:03.770016+00:00
-- url     : https://prove2.me/submissions/61a06afe-c1b6-43bc-95a6-01666bbf496e

import Mathlib
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound : ℕ) (alpha : ℝ) (ha : alpha < 1) :
  tailRiskTVaR w bound bound alpha = (bound : ℝ) := by
  have htail : tailRiskStrictMass w bound bound = 0 := by
    unfold tailRiskStrictMass
    apply Finset.sum_eq_zero
    intro s hs
    have hle : s ≤ bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    simp [not_lt.mpr hle]
  have hpay :
      (∑ s ∈ Finset.range (bound + 1),
        if bound < s then (s : ℝ) * w s else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hle : s ≤ bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    simp [not_lt.mpr hle]
  have hden : 1 - alpha ≠ 0 := by linarith
  unfold tailRiskTVaR tailRiskSelectedLoss tailRiskAtomWeight
  rw [hpay, htail]
  field_simp [hden]
  ring
