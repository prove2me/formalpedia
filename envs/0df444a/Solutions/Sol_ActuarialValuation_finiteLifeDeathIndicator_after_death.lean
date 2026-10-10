-- Prove2me | solution 1 for ActuarialValuation.finiteLifeDeathIndicator_after_death
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:23:05.085347+00:00
-- url     : https://prove2.me/submissions/599a7f4b-d30a-4dc5-8601-9171bda77ea4

import Mathlib
import Definitions.Def_actuarial_finiteLifeDeathIndicator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (K t : ℕ) (h : K < t) :
    finiteLifeDeathIndicator K t = 0 := by
  simp [finiteLifeDeathIndicator, ne_of_lt h]
