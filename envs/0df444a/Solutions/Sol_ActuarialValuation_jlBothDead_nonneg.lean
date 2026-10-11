-- Prove2me | solution 1 for ActuarialValuation.jlBothDead_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:38:37.450985+00:00
-- url     : https://prove2.me/submissions/12f13452-1f2e-414a-8f26-46917f81292d

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlBothDead
open ActuarialValuation

theorem solution(px py : ℝ) (hx : px≤1) (hy : py≤1) : 0≤jlBothDead px py := by
  unfold jlBothDead
  exact mul_nonneg (by linarith) (by linarith)
