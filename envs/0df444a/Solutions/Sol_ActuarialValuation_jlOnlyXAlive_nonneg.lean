-- Prove2me | solution 1 for ActuarialValuation.jlOnlyXAlive_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:18:55.876455+00:00
-- url     : https://prove2.me/submissions/eee3635f-8141-4e0f-ae5a-db71828937d0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlOnlyXAlive
open ActuarialValuation

theorem solution(px py : ℝ) (hx : 0≤px) (hy : py≤1) : 0≤jlOnlyXAlive px py := by
  unfold jlOnlyXAlive
  exact mul_nonneg hx (by linarith)
