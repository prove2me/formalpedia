-- Prove2me | solution 1 for ActuarialValuation.twoStepTransition_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:17:05.818421+00:00
-- url     : https://prove2.me/submissions/f996b98b-6fdc-453b-9f35-295f0ac03359

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_twoStepTransition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P Q : S → S → ℝ)
    (hP : isFiniteMarkovKernel P) (hQ : isFiniteMarkovKernel Q)
    :
    isFiniteMarkovKernel (twoStepTransition P Q) := by
  constructor
  · intro a c
    show 0 ≤ ∑ b : S, P a b * Q b c
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (hP.1 a b) (hQ.1 b c)
  · intro a
    show (∑ c : S, (∑ b : S, P a b * Q b c)) = 1
    rw [Finset.sum_comm]
    calc (∑ b : S, (∑ c : S, P a b * Q b c))
        = ∑ b : S, P a b * (∑ c : S, Q b c) := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ b : S, P a b := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [hQ.2 b, mul_one]
      _ = 1 := hP.2 a
