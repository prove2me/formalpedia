-- Prove2me | solution 1 for ActuarialValuation.cxPairTransform_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:39:26.852159+00:00
-- url     : https://prove2.me/submissions/fe1200bc-dbec-4a98-9500-9bbaa855e09a

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_actuarial_cxPGF
import Definitions.Def_actuarial_cxPairTransform

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f g : ℕ → ℝ) (n m : ℕ) (z : ℝ) : cxPairTransform f g n m z = cxPGF f n z * cxPGF g m z := by
  simp [cxPairTransform, cxPGF, Finset.sum_mul_sum, pow_add,
    mul_assoc, mul_left_comm, mul_comm]
