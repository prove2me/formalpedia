-- Prove2me | solution 1 for ActuarialValuation.cm1LifeSurvival_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:19:03.92998+00:00
-- url     : https://prove2.me/submissions/44ada316-db0c-4baa-81d1-7de3b774ea05

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeSurvival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x n : ℕ) (hl : 0 < l x) (hn : 0 ≤ l (x+n)) : 0 ≤ cm1LifeSurvival l x n := by
  unfold cm1LifeSurvival
  exact div_nonneg hn (le_of_lt hl)
