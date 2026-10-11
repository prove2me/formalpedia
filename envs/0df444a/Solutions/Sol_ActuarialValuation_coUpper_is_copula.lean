-- Prove2me | solution 1 for ActuarialValuation.coUpper_is_copula
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:41:33.58523+00:00
-- url     : https://prove2.me/submissions/8d0e85c6-a24c-45ca-bfca-c94137510e42

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coUpper
import Definitions.Def_actuarial_coIsCopula
open ActuarialValuation

theorem solution: coIsCopula coUpper := by
  unfold coIsCopula coRectangle coUpper
  refine ⟨fun u h0 h1 => ⟨?_, ?_, ?_, ?_⟩, fun u1 u2 v1 v2 h1 h2 h3 h4 h5 h6 => ?_⟩ <;>
    simp only [min_def] <;> split_ifs <;> linarith
