-- Prove2me | solution 1 for ActuarialValuation.ruRuinProb_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:59:19.737284+00:00
-- url     : https://prove2.me/submissions/daf94c25-e0ff-482e-aa1d-b98d3b8e5764

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

theorem solution {m : ℕ} (p : Fin m → ℝ) (A B : Fin m → Prop)
    [DecidablePred A] [DecidablePred B] (hp : ∀ ω, 0 ≤ p ω)
    (hAB : ∀ ω, A ω → B ω) :
    ruRuinProbability p A ≤ ruRuinProbability p B := by
  unfold ruRuinProbability
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hB : B ω
  · by_cases hA : A ω
    · simp [hA, hB]
    · simp only [hA, if_false, hB, if_true]
      exact hp ω
  · have hA : ¬ A ω := fun ha => hB (hAB ω ha)
    simp [hA, hB]
