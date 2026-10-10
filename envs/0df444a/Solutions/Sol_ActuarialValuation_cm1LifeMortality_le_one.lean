-- Prove2me | solution 1 for ActuarialValuation.cm1LifeMortality_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:25:12.03041+00:00
-- url     : https://prove2.me/submissions/b0049288-095d-4703-8ce8-371540564108

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeMortality
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x n : ℕ) (hl : 0 < l x) (hn : 0 ≤ l (x+n)) : cm1LifeMortality l x n ≤ 1 := by
  unfold cm1LifeMortality cm1LifeSurvival
  have h : 0 ≤ l (x + n) / l x := div_nonneg hn (le_of_lt hl)
  linarith
