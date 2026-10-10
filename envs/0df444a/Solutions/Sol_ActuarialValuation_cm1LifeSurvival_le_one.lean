-- Prove2me | solution 1 for ActuarialValuation.cm1LifeSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:19:15.407383+00:00
-- url     : https://prove2.me/submissions/a642ab70-c0bd-44f7-bb89-a1734d08f000

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x n : ℕ) (hl : 0 < l x) (hle : l (x+n) ≤ l x) : cm1LifeSurvival l x n ≤ 1 := by
  unfold cm1LifeSurvival
  exact (div_le_one hl).2 hle
