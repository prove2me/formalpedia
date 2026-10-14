-- Prove2me | solution 1 for ActuarialValuation.clFactorToUltimate_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:55:39.777789+00:00
-- url     : https://prove2.me/submissions/adf46ccc-66f3-404a-b30f-882ab2b3f3e4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clFactorToUltimate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (j n : ℕ) : clFactorToUltimate f j (n+1) = clFactorToUltimate f j n * f (j+n) := by
  simp [clFactorToUltimate, Finset.prod_range_succ]
