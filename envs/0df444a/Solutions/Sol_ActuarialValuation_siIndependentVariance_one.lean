-- Prove2me | solution 1 for ActuarialValuation.siIndependentVariance_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:07:52.71259+00:00
-- url     : https://prove2.me/submissions/0c06b3bb-c61c-4537-84df-63cb8d78672e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_siIndependentVariance
open ActuarialValuation

theorem solution(m s : ℝ) : siIndependentVariance m s 1=s-m^2 := by
  simp [siIndependentVariance]
