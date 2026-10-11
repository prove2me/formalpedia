-- Prove2me | solution 1 for ActuarialValuation.jlOnlyYAlive_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:17:30.317734+00:00
-- url     : https://prove2.me/submissions/0300ccf2-b7f8-421d-8649-fcdbdbc16940

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlOnlyYAlive
open ActuarialValuation

theorem solution(px py : ℝ) (hx : px≤1) (hy : 0≤py) : 0≤jlOnlyYAlive px py := by
  unfold jlOnlyYAlive
  exact mul_nonneg (by linarith) hy
