-- Prove2me | solution 1 for ActuarialValuation.cm1JointLifeAnnuity_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:35.262371+00:00
-- url     : https://prove2.me/submissions/63444c7d-3abe-42c0-b063-5571aefbdf15

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1JointLifeAnnuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount both : ℕ → ℝ) (n : ℕ) : cm1JointLifeAnnuity discount both (n+1) = cm1JointLifeAnnuity discount both n + discount n * both n := by
  simp [cm1JointLifeAnnuity, Finset.sum_range_succ]
