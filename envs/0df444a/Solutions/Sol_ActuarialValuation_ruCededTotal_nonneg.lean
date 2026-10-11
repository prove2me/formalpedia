-- Prove2me | solution 1 for ActuarialValuation.ruCededTotal_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:22:02.945511+00:00
-- url     : https://prove2.me/submissions/1512d56c-0c0b-4db8-825e-d142301ade6b

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ruCededTotal
open ActuarialValuation

theorem solution(x : ℕ → ℝ) (d : ℝ) (n : ℕ) : 0 ≤ ruCededTotal x d n := by
  unfold ruCededTotal
  exact Finset.sum_nonneg (fun k _ => by unfold ruStopLoss; exact le_max_left _ _)
