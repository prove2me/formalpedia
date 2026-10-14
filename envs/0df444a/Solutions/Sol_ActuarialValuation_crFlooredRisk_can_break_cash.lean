-- Prove2me | solution 1 for ActuarialValuation.crFlooredRisk_can_break_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:08:53.145707+00:00
-- url     : https://prove2.me/submissions/e3c748b5-a5ff-419c-86d2-4a02ddfaf9c7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crFlooredRisk

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p q : Fin 2→ℝ) (hp : (∑ i : Fin 2,p i)=1) (hq : (∑ i : Fin 2,q i)=1) : crFlooredRisk p q (fun _=>-1)=0 ∧ crFlooredRisk p q (fun _=>0)=0 := by
  have hc (r : Fin 2 → ℝ) (hr : (∑ i : Fin 2, r i) = 1) :
      crExpected r (fun _ => -1) = -1 := by
    unfold crExpected
    calc
      (∑ i : Fin 2, r i * (-1)) = (∑ i : Fin 2, r i) * (-1) := by
        rw [Finset.sum_mul]
      _ = -1 := by rw [hr]; ring
  have hz (r : Fin 2 → ℝ) :
      crExpected r (fun _ => 0) = 0 := by
    simp [crExpected]
  simp [crFlooredRisk, crScenarioRisk, hc p hp, hc q hq, hz p, hz q]
