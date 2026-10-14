-- Prove2me | solution 1 for ActuarialValuation.cxConvolution_comm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T12:28:07.089702+00:00
-- url     : https://prove2.me/submissions/14e1956c-5a0f-4140-bdbd-5d0db10c9422

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxConvolution
open ActuarialValuation

theorem solution(f g : ℕ → ℝ) (k : ℕ) : cxConvolution f g k = cxConvolution g f k := by
  unfold cxConvolution
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [mul_comm]
  congr 2
  omega
