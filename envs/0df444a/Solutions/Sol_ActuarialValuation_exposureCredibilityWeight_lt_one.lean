-- Prove2me | solution 1 for ActuarialValuation.exposureCredibilityWeight_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:00:55.106723+00:00
-- url     : https://prove2.me/submissions/e3b9347b-e261-4615-8246-007f6f5aea83

import Mathlib.Tactic.Linarith
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
  exposureCredibilityWeight EPV VHM P < 1 := by
  change P * VHM / (P * VHM + EPV) < 1
  have hd : 0 < P * VHM + EPV :=
    add_pos_of_nonneg_of_pos (mul_nonneg hP hV) hE
  apply (div_lt_iff₀ hd).2
  simpa only [one_mul] using
    (show P * VHM < P * VHM + EPV by linarith)
