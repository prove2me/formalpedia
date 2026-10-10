-- Prove2me | solution 1 for ActuarialValuation.wholeLifeFiniteInnovation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:34:05.656002+00:00
-- url     : https://prove2.me/submissions/ff91c82a-bb61-4fa4-aa86-5d948b8737c4

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w rho : ℕ → ℝ) (k : ℕ) :
  wholeLifeFiniteInnovation w rho 0 k = 0 := by
  simp [wholeLifeFiniteInnovation]
