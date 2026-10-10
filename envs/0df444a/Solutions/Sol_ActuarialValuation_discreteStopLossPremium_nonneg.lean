-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossPremium_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:18:12.520985+00:00
-- url     : https://prove2.me/submissions/c2c6f663-dc2a-4a4a-ad95-6040c67d62c6

import Mathlib
import Definitions.Def_actuarial_discreteStopLossPremium
open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ discreteStopLossPremium w bound deductible := by
  unfold discreteStopLossPremium
  exact Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hw s)
