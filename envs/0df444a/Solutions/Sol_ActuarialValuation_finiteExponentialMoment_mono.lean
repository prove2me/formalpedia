-- Prove2me | solution 1 for ActuarialValuation.finiteExponentialMoment_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:25:16.40545+00:00
-- url     : https://prove2.me/submissions/1730ef18-0dcc-41ae-8db3-aa2a7c012767

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_actuarial_finiteExponentialMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ)
    (gamma : ℝ) (hw : ∀ ω, 0 ≤ w ω) (hgamma : 0 ≤ gamma)
    (hXY : ∀ ω, X ω ≤ Y ω) :
    finiteExponentialMoment w X gamma ≤ finiteExponentialMoment w Y gamma := by
  unfold finiteExponentialMoment
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (hw ω)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hXY ω) hgamma)
