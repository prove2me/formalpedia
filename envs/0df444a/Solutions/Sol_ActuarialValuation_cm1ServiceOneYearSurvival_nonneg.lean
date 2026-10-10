-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceOneYearSurvival_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:33:03.38243+00:00
-- url     : https://prove2.me/submissions/3a82ec88-9d71-4704-9191-d7c736219a2d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceOneYearSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (t : ℕ) (ht : 0 < l t) (hn : 0 ≤ l (t+1)) : 0 ≤ cm1ServiceOneYearSurvival l t := by
  dsimp only [cm1ServiceOneYearSurvival]
  exact div_nonneg hn (le_of_lt ht)
