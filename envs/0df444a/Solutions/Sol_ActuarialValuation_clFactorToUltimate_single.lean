-- Prove2me | solution 1 for ActuarialValuation.clFactorToUltimate_single
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:08.912976+00:00
-- url     : https://prove2.me/submissions/f0755a7c-0971-4032-aca3-da1801906e16

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clFactorToUltimate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (j : ℕ) : clFactorToUltimate f j 1 = f j := by
  simp [clFactorToUltimate, Finset.prod_range_succ]
