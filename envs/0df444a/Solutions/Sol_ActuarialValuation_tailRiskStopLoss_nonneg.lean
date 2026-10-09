-- Prove2me | solution 1 for ActuarialValuation.tailRiskStopLoss_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T12:04:41.328001+00:00
-- url     : https://prove2.me/submissions/ea63d18e-8e47-44a4-9ea2-5b586f8da3e6

import Mathlib
import Definitions.Def_actuarial_tailRiskStopLoss

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (bound q : ℕ) (hw : ∀ s, 0 ≤ w s) : 0 ≤ tailRiskStopLoss w bound q := by
  unfold tailRiskStopLoss
  exact Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hw s)
