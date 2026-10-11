-- Prove2me | solution 1 for ActuarialValuation.siIndependentVariance_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:11:41.171076+00:00
-- url     : https://prove2.me/submissions/7081862f-cbe1-4096-94f1-7424f87c621e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siIndependentVariance
open ActuarialValuation

theorem solution(m s : ℝ) : siIndependentVariance m s 0=0 := by
  simp [siIndependentVariance]
