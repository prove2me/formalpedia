-- Prove2me | solution 1 for ActuarialValuation.irCumulative_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:59:58.472603+00:00
-- url     : https://prove2.me/submissions/910dc31d-dc1e-450b-9879-69533c75dedf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irCumulative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (row : ℕ → ℝ) (n : ℕ) : irCumulative row (n+1)=irCumulative row n+row n := by
  unfold irCumulative
  rw [Finset.sum_range_succ]
