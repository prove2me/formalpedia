-- Prove2me | solution 1 for ActuarialValuation.decrementFiniteExposure_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:35:30.335451+00:00
-- url     : https://prove2.me/submissions/6e88d619-5bbd-47e5-b96e-a51a2137fe2c

import Mathlib
import Definitions.Def_actuarial_decrementFiniteExposure
import Definitions.Def_actuarial_decrementCauseInnovation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (n k : ℕ) (d : C) :
  decrementFiniteExposure w rho (n + 1) k d =
    decrementFiniteExposure w rho n k d +
      ∑ c : C, rho n c * decrementCauseInnovation w n c k d := by
  simp [decrementFiniteExposure, Finset.sum_range_succ]
