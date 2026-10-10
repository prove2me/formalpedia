-- Prove2me | solution 1 for ActuarialValuation.pensionEarlyComparator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:25.449442+00:00
-- url     : https://prove2.me/submissions/2f544faa-3f2c-469d-b6a9-4128a2009716

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionEarlyComparator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D p v A : ℝ)
  (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hA : 0 ≤ A) :
  0 ≤ pensionEarlyComparator D p v A := by
  change 0 ≤ D + p * v * A
  exact add_nonneg hD (mul_nonneg (mul_nonneg hp hv) hA)
