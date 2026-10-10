-- Prove2me | solution 1 for ActuarialValuation.poissonSplitJointMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:28:34.373222+00:00
-- url     : https://prove2.me/submissions/82da8354-4fa8-4782-b45a-f3b9bf499c0c

import Mathlib.Tactic.Positivity
import Definitions.Def_actuarial_poissonSplitJointMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate selection : ℝ) (a b : ℕ)
    (hr : 0 ≤ rate) (hp0 : 0 ≤ selection) (hp1 : selection ≤ 1) :
    0 ≤ poissonSplitJointMass rate selection a b := by
  have hp_other : 0 ≤ 1 - selection := sub_nonneg.mpr hp1
  dsimp [poissonSplitJointMass, poissonCountMass]
  positivity
