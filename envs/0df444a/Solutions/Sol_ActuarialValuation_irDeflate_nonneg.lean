-- Prove2me | solution 1 for ActuarialValuation.irDeflate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:58:20.636981+00:00
-- url     : https://prove2.me/submissions/37f1c407-35bd-4a38-a265-f95bff327964

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irDeflate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (claim base hist : ℝ) (hc : 0≤claim) (hb : 0≤base) (hh : 0<hist) : 0≤irDeflate claim base hist := by
  unfold irDeflate
  exact div_nonneg (mul_nonneg hc hb) (le_of_lt hh)
