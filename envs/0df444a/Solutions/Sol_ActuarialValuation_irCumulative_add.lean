-- Prove2me | solution 1 for ActuarialValuation.irCumulative_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:00:17.627031+00:00
-- url     : https://prove2.me/submissions/f4b38c9d-929a-4281-b8d7-cf7e8567993e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_irCumulative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b : ℕ → ℝ) (n : ℕ) : irCumulative (fun j => a j+b j) n=irCumulative a n+irCumulative b n := by
  unfold irCumulative
  rw [Finset.sum_add_distrib]
