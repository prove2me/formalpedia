-- Prove2me | solution 1 for ActuarialValuation.wholeLifeYearInnovation_at
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:33:48.548572+00:00
-- url     : https://prove2.me/submissions/3f9c5a50-d1a8-4b85-a75f-b93bafddd4f5

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (t : ℕ) :
  wholeLifeYearInnovation w t t =
    1 - w t / wholeLifeTailMass w t := by
  simp [wholeLifeYearInnovation]
