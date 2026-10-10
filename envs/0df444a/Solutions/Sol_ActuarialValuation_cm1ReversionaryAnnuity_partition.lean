-- Prove2me | solution 1 for ActuarialValuation.cm1ReversionaryAnnuity_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:57.633068+00:00
-- url     : https://prove2.me/submissions/104b8f02-070c-4e45-b593-f931110ffd77

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SingleLifeAnnuity
import Definitions.Def_actuarial_cm1JointLifeAnnuity
import Definitions.Def_actuarial_cm1ReversionaryAnnuity
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount pY both : ℕ → ℝ) (n : ℕ) : cm1ReversionaryAnnuity discount pY both n + cm1JointLifeAnnuity discount both n = cm1SingleLifeAnnuity discount pY n := by
  unfold cm1ReversionaryAnnuity cm1JointLifeAnnuity cm1SingleLifeAnnuity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  unfold cm1ReversionaryIndicator
  ring
