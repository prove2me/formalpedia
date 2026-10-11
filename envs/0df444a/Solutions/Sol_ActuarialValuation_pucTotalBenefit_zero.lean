-- Prove2me | solution 1 for ActuarialValuation.pucTotalBenefit_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:02:53.815905+00:00
-- url     : https://prove2.me/submissions/cb67e9bd-e572-4341-840f-aa2a1fe7a493

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucTotalBenefit
open ActuarialValuation

theorem solution(u : ℕ → ℝ) : pucTotalBenefit u 0 0 = 0 := by
  simp [pucTotalBenefit, pucAccruedBenefit, pucFutureBenefit]
