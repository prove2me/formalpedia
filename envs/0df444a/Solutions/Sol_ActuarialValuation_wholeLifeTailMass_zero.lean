-- Prove2me | solution 1 for ActuarialValuation.wholeLifeTailMass_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:33:29.515612+00:00
-- url     : https://prove2.me/submissions/8e7f44e4-a2c4-4a39-b898-c3ff18f5aa7a

import Mathlib
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ)
  (h : (∑' k : ℕ, w k) = 1) :
  wholeLifeTailMass w 0 = 1 := by
  simpa [wholeLifeTailMass] using h
