-- Prove2me | solution 1 for ActuarialValuation.twoStepTransition_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:15:13.970369+00:00
-- url     : https://prove2.me/submissions/40ec73d3-736a-4005-94f7-6116c6803099

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_twoStepTransition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P Q : S → S → ℝ)
    (hP : isFiniteMarkovKernel P) (hQ : isFiniteMarkovKernel Q) (a : S)
    :
    (∑ c : S, twoStepTransition P Q a c) = 1 := by
  show (∑ c : S, ∑ b : S, P a b * Q b c) = 1
  rw [Finset.sum_comm]
  calc (∑ b : S, ∑ c : S, P a b * Q b c)
      = ∑ b : S, P a b * (∑ c : S, Q b c) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ b : S, P a b := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [hQ.2 b, mul_one]
    _ = 1 := hP.2 a
