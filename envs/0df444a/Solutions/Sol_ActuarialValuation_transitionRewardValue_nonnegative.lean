-- Prove2me | solution 1 for ActuarialValuation.transitionRewardValue_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:23:20.83621+00:00
-- url     : https://prove2.me/submissions/d6350de2-2635-4374-a45d-6934cfc95556

import Mathlib
import Definitions.Def_actuarial_isFiniteMarkovKernel
import Definitions.Def_actuarial_transitionRewardValue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {S : Type*} [Fintype S] (P : S → S → ℝ) (hP : isFiniteMarkovKernel P) (v : ℝ)
    (hv : 0 ≤ v) (r next : S → ℝ)
    (hr : ∀ b, 0 ≤ r b) (hn : ∀ b, 0 ≤ next b) (a : S)
    :
    0 ≤ transitionRewardValue P v r next a := by
  show 0 ≤ v * (∑ b : S, P a b * (r b + next b))
  apply mul_nonneg hv
  apply Finset.sum_nonneg
  intro b _
  apply mul_nonneg (hP.1 a b) (add_nonneg (hr b) (hn b))
