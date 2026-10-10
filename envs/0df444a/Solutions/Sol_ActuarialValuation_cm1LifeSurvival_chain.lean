-- Prove2me | solution 1 for ActuarialValuation.cm1LifeSurvival_chain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:16:37.985707+00:00
-- url     : https://prove2.me/submissions/58dd04a4-2e8d-4fee-b75c-e3407d9a1bae

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1LifeSurvival
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (x m n : ℕ) (hl : l (x+m) ≠ 0) : cm1LifeSurvival l x (m+n) = cm1LifeSurvival l x m * cm1LifeSurvival l (x+m) n := by
  unfold cm1LifeSurvival
  have hs : x + (m + n) = (x + m) + n := by omega
  rw [hs]
  by_cases hx : l x = 0
  · simp [hx]
  · field_simp [hx, hl] <;> ring
