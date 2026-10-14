-- Prove2me | solution 1 for ActuarialValuation.ruRuinProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:05:07.268014+00:00
-- url     : https://prove2.me/submissions/758b0ce5-a8a3-42f6-83cb-16b39ea0586b

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_ruRuinProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (ruin : Fin m → Prop)
    [DecidablePred ruin] (hp : ∀ ω, 0 ≤ p ω) :
    0 ≤ ruRuinProbability p ruin := by
  unfold ruRuinProbability
  apply Finset.sum_nonneg
  intro ω hω
  by_cases h : ruin ω
  · simp only [h, if_true]
    exact hp ω
  · simp only [h, if_false]
    exact le_refl 0
