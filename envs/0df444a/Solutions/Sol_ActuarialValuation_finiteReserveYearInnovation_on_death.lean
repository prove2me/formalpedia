-- Prove2me | solution 1 for ActuarialValuation.finiteReserveYearInnovation_on_death
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:24:57.086031+00:00
-- url     : https://prove2.me/submissions/4d3c041a-c0fd-4b5a-b896-977b09bbbf01

import Mathlib
import Definitions.Def_actuarial_finiteReserveYearInnovation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K t : ℕ) (q : ℕ → ℝ) (h : K = t) :
    finiteReserveYearInnovation K t q = 1 - q t := by
  simp [finiteReserveYearInnovation, finiteLifeDeathIndicator,
    finiteLifeInForceIndicator, h]
