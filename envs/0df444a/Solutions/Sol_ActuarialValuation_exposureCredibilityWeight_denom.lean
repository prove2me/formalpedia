-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityWeight_denom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:01:01.300326+00:00
-- url     : https://prove2.me/submissions/d898c468-604e-4e6c-8745-a19fb4de63f3

import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (EPV VHM P : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  (P * VHM + EPV) * exposureCredibilityWeight EPV VHM P =
    P * VHM := by
  change (P * VHM + EPV) *
    (P * VHM / (P * VHM + EPV)) = P * VHM
  have hd : P * VHM + EPV ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (mul_nonneg hP hV) hE)
  field_simp [hd]
