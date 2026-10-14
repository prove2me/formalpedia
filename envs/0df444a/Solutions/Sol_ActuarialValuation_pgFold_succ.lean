-- Prove2me | solution 1 for ActuarialValuation.pgFold_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:36:29.397399+00:00
-- url     : https://prove2.me/submissions/78b2488a-4c47-453f-91cb-c4795dd7f4f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pgConvolve
import Definitions.Def_actuarial_pgFold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n k : ℕ) : pgFold f (n+1) k = pgConvolve f (pgFold f n) k := by
  rfl
