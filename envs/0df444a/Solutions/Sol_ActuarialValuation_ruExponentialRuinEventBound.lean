-- Prove2me | solution 1 for ActuarialValuation.ruExponentialRuinEventBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T13:20:35.467987+00:00
-- url     : https://prove2.me/submissions/2525e86b-73ec-4b98-bd30-0d9f86e1fda5

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruRuinProbability
import Definitions.Def_actuarial_ruTerminalExponentialMean
import Definitions.Def_actuarial_ruExponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (terminal : Fin m → ℝ) (R : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hR : 0 < R) :
    ruRuinProbability p (fun ω => terminal ω < 0)
      ≤ ruTerminalExponentialMean p R terminal := by
  unfold ruRuinProbability ruTerminalExponentialMean ruMean ruExponential
  apply Finset.sum_le_sum
  intro ω hω
  by_cases h : terminal ω < 0
  · simp only [h, if_true]
    have h3 : R * terminal ω < 0 := mul_neg_of_pos_of_neg hR h
    have ege : (1 : ℝ) ≤ Real.exp (-R * terminal ω) := by
      have h2 := Real.add_one_le_exp (-R * terminal ω)
      nlinarith
    calc p ω = p ω * 1 := (mul_one _).symm
      _ ≤ p ω * Real.exp (-R * terminal ω) :=
          mul_le_mul_of_nonneg_left ege (hp ω)
  · simp only [h, if_false]
    exact mul_nonneg (hp ω) (le_of_lt (Real.exp_pos _))
