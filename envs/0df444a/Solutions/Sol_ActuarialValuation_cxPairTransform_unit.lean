-- Prove2me | solution 1 for ActuarialValuation.cxPairTransform_unit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T14:39:37.258117+00:00
-- url     : https://prove2.me/submissions/c9a2632f-77bf-44c3-b4c8-ff6f75ee0c29

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPairTransform
import Definitions.Def_actuarial_cxMass
open ActuarialValuation

theorem solution(f g : ℕ → ℝ) (n m : ℕ) : cxPairTransform f g n m 1 = cxMass f n * cxMass g m := by
  unfold cxPairTransform cxMass
  simp only [one_pow, mul_one]
  rw [Finset.sum_mul_sum]
