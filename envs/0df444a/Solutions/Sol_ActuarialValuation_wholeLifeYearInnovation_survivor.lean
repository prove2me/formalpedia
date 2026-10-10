-- Prove2me | solution 1 for ActuarialValuation.wholeLifeYearInnovation_survivor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:33:55.936978+00:00
-- url     : https://prove2.me/submissions/36cc5e1f-ce77-4059-bba5-f84315defa64

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation
import Definitions.Def_actuarial_wholeLifeTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (t k : ℕ)
  (h : t < k) :
  wholeLifeYearInnovation w t k =
    -(w t / wholeLifeTailMass w t) := by
  have hne : k ≠ t := ne_of_gt h
  have hle : t ≤ k := le_of_lt h
  simp [wholeLifeYearInnovation, hne, hle]
