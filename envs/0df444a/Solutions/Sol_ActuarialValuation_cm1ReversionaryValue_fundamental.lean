-- Prove2me | solution 1 for ActuarialValuation.cm1ReversionaryValue_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:17:32.802417+00:00
-- url     : https://prove2.me/submissions/21ca68c7-a7f2-4289-ad22-77a6fa99e860

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_cm1SingleLifeAnnuity
import Definitions.Def_actuarial_cm1JointLifeAnnuity
import Definitions.Def_actuarial_cm1ReversionaryAnnuity
import Definitions.Def_actuarial_cm1LastSurvivorAnnuity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (discount pX pY both : ℕ → ℝ) (n : ℕ) (hd : ∀ t ∈ Finset.range n, 0 ≤ discount t) (hjoint : ∀ t ∈ Finset.range n, 0 ≤ both t ∧ both t ≤ pX t ∧ both t ≤ pY t) :
  (0 ≤ cm1ReversionaryAnnuity discount pY both n) ∧
  (cm1ReversionaryAnnuity discount pY both n + cm1JointLifeAnnuity discount both n = cm1SingleLifeAnnuity discount pY n) ∧
  (cm1LastSurvivorAnnuity discount pX pY both n + cm1JointLifeAnnuity discount both n = cm1SingleLifeAnnuity discount pX n + cm1SingleLifeAnnuity discount pY n) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold cm1ReversionaryAnnuity
    apply Finset.sum_nonneg
    intro t ht
    apply mul_nonneg (hd t ht)
    unfold cm1ReversionaryIndicator
    exact sub_nonneg.mpr (hjoint t ht).2.2
  · unfold cm1ReversionaryAnnuity cm1JointLifeAnnuity cm1SingleLifeAnnuity
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    unfold cm1ReversionaryIndicator
    ring
  · unfold cm1LastSurvivorAnnuity cm1JointLifeAnnuity cm1SingleLifeAnnuity
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    unfold cm1LastSurvivorIndicator
    ring
