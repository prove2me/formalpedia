-- Prove2me | solution 1 for ActuarialValuation.poissonSuperposedRate_comm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:28:18.349298+00:00
-- url     : https://prove2.me/submissions/4ba19ec0-4b9e-4cce-ad52-f51c3a3b025a

import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_poissonSuperposedRate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℝ) :
    poissonSuperposedRate a b = poissonSuperposedRate b a := by
  dsimp [poissonSuperposedRate]
  ring
