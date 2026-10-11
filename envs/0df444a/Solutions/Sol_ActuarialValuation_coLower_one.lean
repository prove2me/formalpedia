-- Prove2me | solution 1 for ActuarialValuation.coLower_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T06:14:22.162493+00:00
-- url     : https://prove2.me/submissions/03fec0af-5c0b-463f-b26b-b5a7d04d6ed0

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coLower
open ActuarialValuation

theorem solution(u : ℝ) (h0 : 0≤u) (h1 : u≤1) : coLower u 1=u := by
  unfold coLower
  rw [show u + 1 - 1 = u by ring]
  exact max_eq_right h0
