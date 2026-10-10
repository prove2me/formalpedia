-- Prove2me | solution 2 for ActuarialValuation.finiteLifeDeathIndicator_after_death
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:23:51.35133+00:00
-- url     : https://prove2.me/submissions/31041a90-d31d-41f4-8448-8a6c052fd430

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
open ActuarialValuation

theorem solution (K t : ℕ) (h : K < t) : finiteLifeDeathIndicator K t = 0 := by
  simp [finiteLifeDeathIndicator, show K ≠ t from ne_of_lt h]
