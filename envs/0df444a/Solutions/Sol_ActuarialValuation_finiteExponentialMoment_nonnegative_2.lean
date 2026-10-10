-- Prove2me | solution 2 for ActuarialValuation.finiteExponentialMoment_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:30:36.336276+00:00
-- url     : https://prove2.me/submissions/d251f53d-d6c8-415e-9105-c5d7ab7b59c3

import Mathlib
import Definitions.Def_actuarial_finiteExponentialMoment
open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (gamma : ℝ)
  (hw : ∀ ω, 0 ≤ w ω)
  :
  0 ≤ finiteExponentialMoment w X gamma := by
  unfold finiteExponentialMoment
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (Real.exp_pos _).le
