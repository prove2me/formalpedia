-- Prove2me | solution 1 for ActuarialValuation.ruTwoScenarioRuin_all
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T16:31:22.238811+00:00
-- url     : https://prove2.me/submissions/68cdedd7-55be-4fd9-98af-b7e927cefbd6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruTwoScenarioRuin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q : ℝ) :
    ruTwoScenarioRuin p q true true = p+q := by
  simp [ruTwoScenarioRuin]
