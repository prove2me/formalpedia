-- Prove2me | solution 1 for ActuarialValuation.cm1GrossLevelPremium_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:36.578975+00:00
-- url     : https://prove2.me/submissions/916f7a3d-e30b-43c2-a25a-2a2f48574928

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1GrossLevelPremium

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (B E A : ℝ) (hA : A ≠ 0) : cm1GrossLevelPremium B E A * A = B + E := by
  unfold cm1GrossLevelPremium
  field_simp [hA]
