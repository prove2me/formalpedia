-- Prove2me | solution 1 for ActuarialValuation.mackSquaredResidual_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:35:19.969158+00:00
-- url     : https://prove2.me/submissions/d9ffa3f7-2791-4037-8c0c-3b03f9b43c5f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackSquaredResidual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (actual predicted : ℝ) : 0 ≤ mackSquaredResidual actual predicted := by
  unfold mackSquaredResidual
  exact sq_nonneg _
