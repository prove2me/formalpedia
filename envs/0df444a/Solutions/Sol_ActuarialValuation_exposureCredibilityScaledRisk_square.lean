-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityScaledRisk_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:02:26.684126+00:00
-- url     : https://prove2.me/submissions/9c95b8c1-17de-4cb6-8572-68f5cf282841

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight
import Definitions.Def_actuarial_exposureCredibilityScaledRisk

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P z : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  exposureCredibilityScaledRisk EPV VHM P z =
    (P * VHM + EPV) *
      (z - exposureCredibilityWeight EPV VHM P) ^ 2 +
    P * VHM * EPV / (P * VHM + EPV) := by
  unfold exposureCredibilityScaledRisk exposureCredibilityWeight
  have hd : P * VHM + EPV ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg hP hV) hE)
  field_simp [hd] <;> ring
