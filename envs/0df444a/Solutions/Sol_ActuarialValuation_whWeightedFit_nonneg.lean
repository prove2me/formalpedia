-- Prove2me | solution 1 for ActuarialValuation.whWeightedFit_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:18:55.300275+00:00
-- url     : https://prove2.me/submissions/565dd3fd-ef3d-4735-82af-5ea161b94c65

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whWeightedFit
open ActuarialValuation

theorem solution(w g q : ℝ) (hw : 0 ≤ w) : 0 ≤ whWeightedFit w g q := by
  unfold whWeightedFit whSquaredResidual
  exact mul_nonneg hw (sq_nonneg _)
