-- Prove2me | solution 1 for ActuarialValuation.finiteExponentialMoment_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:09.935535+00:00
-- url     : https://prove2.me/submissions/c89ab0e3-2716-4f42-879f-1f87583183ce

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_finiteExponentialMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (gamma c : ℝ) (hsum : (∑ ω : Ω, w ω) = 1) :
    finiteExponentialMoment w (fun _ => c) gamma =
      Real.exp (gamma * c) := by
  unfold finiteExponentialMoment
  calc
    (∑ ω : Ω, w ω * Real.exp (gamma * c)) =
      (∑ ω : Ω, w ω) * Real.exp (gamma * c) := by
        rw [Finset.sum_mul]
    _ = Real.exp (gamma * c) := by rw [hsum, one_mul]
