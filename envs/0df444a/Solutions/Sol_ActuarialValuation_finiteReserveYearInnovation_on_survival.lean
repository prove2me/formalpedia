-- Prove2me | solution 1 for ActuarialValuation.finiteReserveYearInnovation_on_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:24:50.704929+00:00
-- url     : https://prove2.me/submissions/55e89157-ff1b-43c2-bd77-fdae0fa4100b

import Mathlib
import Definitions.Def_actuarial_finiteReserveYearInnovation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K t : ℕ) (q : ℕ → ℝ) (h : t < K) :
    finiteReserveYearInnovation K t q = -q t := by
  simp [finiteReserveYearInnovation, finiteLifeDeathIndicator,
    finiteLifeInForceIndicator, ne_of_gt h, Nat.le_of_lt h]
