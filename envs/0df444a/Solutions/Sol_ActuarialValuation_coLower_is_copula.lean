-- Prove2me | solution 1 for ActuarialValuation.coLower_is_copula
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:41:31.622852+00:00
-- url     : https://prove2.me/submissions/19ecc40b-023e-4806-9213-37bb10d2033c

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coLower
import Definitions.Def_actuarial_coIsCopula
open ActuarialValuation

theorem solution: coIsCopula coLower := by
  unfold coIsCopula coRectangle coLower
  refine ⟨fun u h0 h1 => ⟨?_, ?_, ?_, ?_⟩, fun u1 u2 v1 v2 h1 h2 h3 h4 h5 h6 => ?_⟩ <;>
    simp only [max_def] <;> split_ifs <;> linarith
