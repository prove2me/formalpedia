-- Prove2me | solution 1 for ActuarialValuation.pensionEarlyFactor_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:44.654756+00:00
-- url     : https://prove2.me/submissions/aedac437-72c6-45e2-bae0-472a9652f026

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionEarlyFactor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D A f : ℝ)
  (hA : A ≠ 0) (heq : f * A = D) : f = pensionEarlyFactor D A := by
  change f = D / A
  exact (eq_div_iff hA).2 heq
