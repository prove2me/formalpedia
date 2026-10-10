-- Prove2me | solution 1 for ActuarialValuation.tailRiskStopLoss_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:40:45.675792+00:00
-- url     : https://prove2.me/submissions/f043aa37-c188-4704-8c05-8ce2386b1e04

import Mathlib
import Definitions.Def_actuarial_tailRiskStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (bound q : ℕ)
  (h : bound ≤ q) : tailRiskStopLoss w bound q = 0 := by
  unfold tailRiskStopLoss
  apply Finset.sum_eq_zero
  intro s hs
  have hsle : s ≤ bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hle : s ≤ q := le_trans hsle h
  simp [Nat.sub_eq_zero_of_le hle]
