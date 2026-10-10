-- Prove2me | solution 1 for ActuarialValuation.pensionEarlyAdjustedValue_equivalent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:38.906974+00:00
-- url     : https://prove2.me/submissions/1ab0822e-2755-456a-bfc0-1250e9b91f27

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionEarlyAdjustedValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (D A : ℝ)
  (hA : A ≠ 0) : pensionEarlyAdjustedValue D A = D := by
  change (D / A) * A = D
  field_simp [hA] <;> ring
