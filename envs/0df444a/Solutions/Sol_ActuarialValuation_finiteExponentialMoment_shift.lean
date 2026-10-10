-- Prove2me | solution 1 for ActuarialValuation.finiteExponentialMoment_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:20.640175+00:00
-- url     : https://prove2.me/submissions/9c8f2e32-c5d6-400a-b00b-dd3764e70396

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_finiteExponentialMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ)
    (gamma c : ℝ) :
    finiteExponentialMoment w (fun ω => X ω + c) gamma =
      Real.exp (gamma * c) * finiteExponentialMoment w X gamma := by
  unfold finiteExponentialMoment
  calc
    (∑ ω : Ω, w ω * Real.exp (gamma * (X ω + c))) =
      ∑ ω : Ω, Real.exp (gamma * c) *
        (w ω * Real.exp (gamma * X ω)) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [mul_add, Real.exp_add]
          ring
    _ = Real.exp (gamma * c) *
        (∑ ω : Ω, w ω * Real.exp (gamma * X ω)) := by
          rw [Finset.mul_sum]
