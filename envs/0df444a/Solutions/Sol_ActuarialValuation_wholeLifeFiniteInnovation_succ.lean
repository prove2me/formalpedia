-- Prove2me | solution 1 for ActuarialValuation.wholeLifeFiniteInnovation_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:34:12.707138+00:00
-- url     : https://prove2.me/submissions/bfd3f496-1bab-4eef-b076-1149b86dd1ae

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation
import Definitions.Def_actuarial_wholeLifeYearInnovation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w rho : ℕ → ℝ) (n k : ℕ) :
  wholeLifeFiniteInnovation w rho (n + 1) k =
    wholeLifeFiniteInnovation w rho n k +
      rho n * wholeLifeYearInnovation w n k := by
  simp [wholeLifeFiniteInnovation, Finset.sum_range_succ]
