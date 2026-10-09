-- Prove2me | solution 1 for ActuarialValuation.twoStepTransition_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:15:12.363526+00:00
-- url     : https://prove2.me/submissions/e6332b9a-f29b-440b-a57b-8a5f7cd4ea5e

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_twoStepTransition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P Q : S → S → ℝ)
    (hP : isFiniteMarkovKernel P) (hQ : isFiniteMarkovKernel Q) (a c : S)
    :
    0 ≤ twoStepTransition P Q a c := by
  show 0 ≤ ∑ b : S, P a b * Q b c
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (hP.1 a b) (hQ.1 b c)
