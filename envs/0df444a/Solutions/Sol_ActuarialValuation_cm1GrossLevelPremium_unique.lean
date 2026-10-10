-- Prove2me | solution 1 for ActuarialValuation.cm1GrossLevelPremium_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:49.400203+00:00
-- url     : https://prove2.me/submissions/3a020682-0084-487f-b858-5380d0dec980

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1GrossLevelPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B E A G : ℝ) (hA : A ≠ 0) (hG : G * A = B+E) : G = cm1GrossLevelPremium B E A := by
  unfold cm1GrossLevelPremium
  apply (eq_div_iff hA).2
  exact hG
