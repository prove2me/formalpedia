-- Prove2me | solution 1 for ActuarialValuation.cm1DeferredDeath_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:40.651411+00:00
-- url     : https://prove2.me/submissions/aeecd0b1-b928-4ae3-9f26-a98481cc3456

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1DeferredDeath
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x k n : ℕ) (hx : 0 < l x) (hk : 0 < l (x+k)) (hle : l (x+k+n) ≤ l (x+k)) (hn : 0 ≤ l (x+k)) : 0 ≤ cm1DeferredDeath l x k n := by
  unfold cm1DeferredDeath
  apply mul_nonneg
  · unfold cm1LifeSurvival
    exact div_nonneg (le_of_lt hk) (le_of_lt hx)
  · unfold cm1LifeMortality cm1LifeSurvival
    have hh : l (x+k+n) / l (x+k) ≤ 1 := (div_le_one hk).2 hle
    linarith
