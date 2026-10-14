-- Prove2me | solution 1 for ActuarialValuation.ruRuinProb_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:59:02.256979+00:00
-- url     : https://prove2.me/submissions/ac557345-4f12-4626-b004-9a3660c15d30

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
    [DecidablePred ruin] (hp : ∀ ω, 0 ≤ p ω) (hn : (∑ ω : Fin m, p ω) = 1) :
    ruRuinProbability p ruin ≤ 1 := by
  unfold ruRuinProbability
  calc (∑ ω : Fin m, (if ruin ω then p ω else 0))
      ≤ ∑ ω : Fin m, p ω := by
        apply Finset.sum_le_sum
        intro ω hω
        by_cases h : ruin ω
        · simp [h]
        · simp only [h, if_false]
          exact hp ω
    _ = 1 := hn
