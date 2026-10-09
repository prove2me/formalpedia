-- Prove2me | solution 1 for ActuarialValuation.transitionRewardValue_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:19:39.345255+00:00
-- url     : https://prove2.me/submissions/72d57d3f-e656-45f1-b44c-9c48884ab937

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_transitionRewardValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P : S → S → ℝ) (hP : isFiniteMarkovKernel P) (v c : ℝ) (a : S)
    :
    transitionRewardValue P v (fun _ => c) (fun _ => 0) a = v * c := by
  have hsum : (∑ b : S, P a b * (c + 0)) = c := by
    simp only [add_zero]
    rw [← Finset.sum_mul, hP.2 a, one_mul]
  show v * (∑ b : S, P a b * (c + 0)) = v * c
  rw [hsum]
