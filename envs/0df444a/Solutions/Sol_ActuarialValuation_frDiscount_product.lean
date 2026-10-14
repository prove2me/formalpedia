-- Prove2me | solution 1 for ActuarialValuation.frDiscount_product
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T08:17:38.659554+00:00
-- url     : https://prove2.me/submissions/aa506a67-5a67-469d-8514-078b4438faec

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDiscount
open ActuarialValuation

theorem solution(delta s t : ℝ) : frDiscount delta (s+t) = frDiscount delta s * frDiscount delta t := by
  unfold frDiscount
  rw [<- Real.exp_add]
  ring_nf
