-- Prove2me | solution 1 for ActuarialValuation.coLower_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:25:26.829705+00:00
-- url     : https://prove2.me/submissions/c896f0b5-8b29-4bbc-aac0-a3d77ddddb03

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coLower
open ActuarialValuation

theorem solution(u : ℝ) (h0 : 0≤u) (h1 : u≤1) : coLower u 0=0 := by
  unfold coLower
  exact max_eq_left (by linarith)
