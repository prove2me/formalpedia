-- Prove2me | solution 1 for ActuarialValuation.wholeLifeYearInnovation_after
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:33:39.870997+00:00
-- url     : https://prove2.me/submissions/f781a147-c35e-42e6-9bab-8a41d5060994

import Mathlib
import Definitions.Def_actuarial_wholeLifeYearInnovation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w : ℕ → ℝ) (t k : ℕ)
  (h : k < t) : wholeLifeYearInnovation w t k = 0 := by
  have hne : k ≠ t := ne_of_lt h
  have hnot : ¬ t ≤ k := not_le.mpr h
  simp [wholeLifeYearInnovation, hne, hnot]
