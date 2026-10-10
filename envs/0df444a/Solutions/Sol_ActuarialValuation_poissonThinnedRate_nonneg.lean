-- Prove2me | solution 1 for ActuarialValuation.poissonThinnedRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:28:03.336652+00:00
-- url     : https://prove2.me/submissions/5582ed3b-27ee-4278-b6ba-ef79c94ba0a7

import Mathlib
import Definitions.Def_actuarial_poissonThinnedRate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate selection : ℝ) (hr : 0 ≤ rate) (hp : 0 ≤ selection) :
    0 ≤ poissonThinnedRate rate selection := by
  exact mul_nonneg hr hp
