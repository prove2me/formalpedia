-- Prove2me | solution 1 for ActuarialValuation.jlBothAlive_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:08:09.670621+00:00
-- url     : https://prove2.me/submissions/b0bd8a2c-201f-4d23-a0fb-f64037c398de

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlBothAlive
open ActuarialValuation

theorem solution(px py : ℝ) : jlBothAlive px py=jlBothAlive py px := by
  unfold jlBothAlive
  ring
