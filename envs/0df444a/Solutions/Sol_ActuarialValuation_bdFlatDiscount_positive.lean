-- Prove2me | solution 1 for ActuarialValuation.bdFlatDiscount_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:04:05.542828+00:00
-- url     : https://prove2.me/submissions/3fec3d4a-266b-41d7-bf67-36f40ec20922

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_bdFlatDiscount
open ActuarialValuation

theorem solution(R : ℝ) (t : ℕ) (h : 0 < R) : 0 < bdFlatDiscount R t := by
  unfold bdFlatDiscount
  positivity
