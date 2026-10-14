-- Prove2me | solution 1 for ActuarialValuation.pgAggregateCDF_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:58:02.112994+00:00
-- url     : https://prove2.me/submissions/d5009cb9-7994-4356-8fa2-6c6ddf12082e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgAggregate
import Definitions.Def_actuarial_pgAggregateCDF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p f : ℕ → ℝ) (m k : ℕ) :
    pgAggregateCDF p f m (k+1) =
      pgAggregateCDF p f m k + pgAggregate p f m (k+1) := by
  simp only [pgAggregateCDF, Finset.sum_range_succ]
