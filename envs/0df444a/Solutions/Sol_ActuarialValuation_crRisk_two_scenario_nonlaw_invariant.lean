-- Prove2me | solution 1 for ActuarialValuation.crRisk_two_scenario_nonlaw_invariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:17:01.406461+00:00
-- url     : https://prove2.me/submissions/7491625f-2390-4c0a-b643-b3b5ee9856de

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crScenarioRisk

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q X Y : Fin 2→ℝ) (hp : p 0=1/2 ∧ p 1=1/2) (hq : q 0=3/4 ∧ q 1=1/4) (hX : X 0=1 ∧ X 1=0) (hY : Y 0=0 ∧ Y 1=1) : crExpected p X=crExpected p Y ∧ crScenarioRisk p q X=3/4 ∧ crScenarioRisk p q Y=1/2 := by
  have hpx : crExpected p X = (1/2 : ℝ) := by
    norm_num [crExpected, Fin.sum_univ_two, hp.1, hp.2, hX.1, hX.2]
  have hpy : crExpected p Y = (1/2 : ℝ) := by
    norm_num [crExpected, Fin.sum_univ_two, hp.1, hp.2, hY.1, hY.2]
  have hqx : crExpected q X = (3/4 : ℝ) := by
    norm_num [crExpected, Fin.sum_univ_two, hq.1, hq.2, hX.1, hX.2]
  have hqy : crExpected q Y = (1/4 : ℝ) := by
    norm_num [crExpected, Fin.sum_univ_two, hq.1, hq.2, hY.1, hY.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpx, hpy]
  · unfold crScenarioRisk
    rw [hpx, hqx]
    exact max_eq_right (by norm_num : (1/2 : ℝ) ≤ (3/4 : ℝ))
  · unfold crScenarioRisk
    rw [hpy, hqy]
    exact max_eq_left (by norm_num : (1/4 : ℝ) ≤ (1/2 : ℝ))
