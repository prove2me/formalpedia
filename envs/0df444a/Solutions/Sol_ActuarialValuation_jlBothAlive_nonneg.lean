-- Prove2me | solution 1 for ActuarialValuation.jlBothAlive_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:58:23.942202+00:00
-- url     : https://prove2.me/submissions/1de4e6ca-9d8f-4c15-a08f-916186892089

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlBothAlive
open ActuarialValuation

theorem solution(px py : ℝ) (hx : 0≤px) (hy : 0≤py) : 0≤jlBothAlive px py := by
  unfold jlBothAlive
  exact mul_nonneg hx hy
