-- Prove2me | solution 1 for ActuarialValuation.finiteExponentialMoment_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:01.327821+00:00
-- url     : https://prove2.me/submissions/c8ffde26-98d7-4c69-bf22-f91ea5f129ff

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_finiteExponentialMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (gamma : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) :
    0 ≤ finiteExponentialMoment w X gamma := by
  unfold finiteExponentialMoment
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (hw ω) (le_of_lt (Real.exp_pos _))
