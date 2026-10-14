-- Prove2me | solution 1 for ActuarialValuation.coInd_upper_ratio
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:48:13.808983+00:00
-- url     : https://prove2.me/submissions/12363126-5f51-4e69-81ad-ca3e00fa4c51

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coInd
import Definitions.Def_actuarial_coUpperRatio
open ActuarialValuation

theorem solution(u : ℝ) (hu : u≠1) : coUpperRatio coInd u=1-u := by
  have h1 : (1 : ℝ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  unfold coUpperRatio coTailJoint coInd
  field_simp
  ring
