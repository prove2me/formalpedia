-- Prove2me | solution 1 for ActuarialValuation.pucFutureBenefit_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:07:08.611298+00:00
-- url     : https://prove2.me/submissions/fc077f34-0293-4fd1-bd1b-803d1f4262ab

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucFutureBenefit
open ActuarialValuation

theorem solution(u : ℕ → ℝ) (n : ℕ) : pucFutureBenefit u n 0 = 0 := by
  simp [pucFutureBenefit]
