-- Prove2me | solution 1 for ActuarialValuation.decrementFiniteExposure_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:35:43.191652+00:00
-- url     : https://prove2.me/submissions/094619a8-e0c6-4a64-858d-34719c69a4c6

import Mathlib
import Definitions.Def_actuarial_decrementFiniteExposure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (k : ℕ) (d : C) :
  decrementFiniteExposure w rho 0 k d = 0 := by
  simp [decrementFiniteExposure]
