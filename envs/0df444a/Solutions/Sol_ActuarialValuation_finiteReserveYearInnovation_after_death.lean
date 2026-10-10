-- Prove2me | solution 1 for ActuarialValuation.finiteReserveYearInnovation_after_death
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:24:37.550957+00:00
-- url     : https://prove2.me/submissions/2108e2f2-844b-4b63-b229-ad516a2e1da2

import Mathlib
import Definitions.Def_actuarial_finiteReserveYearInnovation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K t : ℕ) (q : ℕ → ℝ) (h : K < t) :
    finiteReserveYearInnovation K t q = 0 := by
  simp [finiteReserveYearInnovation, finiteLifeDeathIndicator,
    finiteLifeInForceIndicator, ne_of_lt h, Nat.not_le.mpr h]
