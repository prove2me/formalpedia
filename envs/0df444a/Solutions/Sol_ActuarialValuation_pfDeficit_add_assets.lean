-- Prove2me | solution 1 for ActuarialValuation.pfDeficit_add_assets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:55:51.260704+00:00
-- url     : https://prove2.me/submissions/bb4094c0-829a-4c78-8bdd-d57cc4a807f4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pfDeficit
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (liability assets extra : ℝ) : pfDeficit liability (assets+extra)=pfDeficit liability assets-extra := by
  unfold pfDeficit
  ring
