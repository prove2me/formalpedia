-- Prove2me | solution 1 for ActuarialValuation.finiteLifeInForceIndicator_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:11:38.513249+00:00
-- url     : https://prove2.me/submissions/371803d7-2108-4184-ae97-587914eace8a

import Mathlib
import Definitions.Def_actuarial_finiteLifeInForceIndicator
open ActuarialValuation

theorem solution (K : ℕ) : finiteLifeInForceIndicator K 0 = 1 := by
  simp [finiteLifeInForceIndicator, Nat.zero_le]
