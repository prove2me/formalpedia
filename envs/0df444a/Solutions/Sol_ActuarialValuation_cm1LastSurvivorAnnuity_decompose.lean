-- Prove2me | solution 1 for ActuarialValuation.cm1LastSurvivorAnnuity_decompose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:49.343633+00:00
-- url     : https://prove2.me/submissions/645d3c19-1dbe-4c82-8673-1475f0801f68

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SingleLifeAnnuity
import Definitions.Def_actuarial_cm1JointLifeAnnuity
import Definitions.Def_actuarial_cm1LastSurvivorAnnuity
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount pX pY both : ℕ → ℝ) (n : ℕ) : cm1LastSurvivorAnnuity discount pX pY both n + cm1JointLifeAnnuity discount both n = cm1SingleLifeAnnuity discount pX n + cm1SingleLifeAnnuity discount pY n := by
  unfold cm1LastSurvivorAnnuity cm1JointLifeAnnuity cm1SingleLifeAnnuity
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  unfold cm1LastSurvivorIndicator
  ring
