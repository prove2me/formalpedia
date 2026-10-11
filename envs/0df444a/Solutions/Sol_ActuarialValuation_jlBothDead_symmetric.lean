-- Prove2me | solution 1 for ActuarialValuation.jlBothDead_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T09:12:50.495963+00:00
-- url     : https://prove2.me/submissions/ab444ada-6107-4395-b1fe-75df518ff675

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Definitions.Def_actuarial_jlBothDead
open ActuarialValuation

theorem solution(px py : ℝ) : jlBothDead px py=jlBothDead py px := by
  unfold jlBothDead
  ring
