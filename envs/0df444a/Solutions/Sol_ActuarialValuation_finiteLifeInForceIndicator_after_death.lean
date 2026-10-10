-- Prove2me | solution 1 for ActuarialValuation.finiteLifeInForceIndicator_after_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:11:37.448595+00:00
-- url     : https://prove2.me/submissions/d66dd01b-8b47-4122-aedf-905680e01c4d

import Mathlib
import Definitions.Def_actuarial_finiteLifeInForceIndicator
open ActuarialValuation

theorem solution (K t : ℕ) (h : K < t) : finiteLifeInForceIndicator K t = 0 := by
  simp [finiteLifeInForceIndicator, not_le.mpr h]
