-- Prove2me | solution 1 for ActuarialValuation.cm1LifeSurvival_mortality_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:44.432839+00:00
-- url     : https://prove2.me/submissions/15646abc-96a7-4056-add5-3e3c25941a4c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeSurvival
import Definitions.Def_actuarial_cm1LifeMortality
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x n : ℕ) : cm1LifeSurvival l x n + cm1LifeMortality l x n = 1 := by
  unfold cm1LifeMortality
  ring
