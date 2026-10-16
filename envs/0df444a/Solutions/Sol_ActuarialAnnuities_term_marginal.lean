-- Prove2me | solution 1 for ActuarialAnnuities.term_marginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:09:06.533363+00:00
-- url     : https://prove2.me/submissions/cf2e3efb-9ce7-4a45-8819-ff4999ae2c6e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    bSurvivalPV h a (n+1) g delta v b p -
      bSurvivalPV h a n g delta v b p =
    if a+n < h then
      b (a+n)*v^(a+n+delta)*
        (if n < g then bSurvival h p a else bSurvival h p (a+n+delta))
    else 0 := by
  classical
  let F : ℕ → ℝ := fun j =>
    b j * v^(j+delta) *
      (if j < a+g then bSurvival h p a else bSurvival h p (j+delta))
  change (∑ j ∈ Finset.range h,
      if a ≤ j ∧ j < a+(n+1) then F j else 0) -
    (∑ j ∈ Finset.range h,
      if a ≤ j ∧ j < a+n then F j else 0) = _
  rw [← Finset.sum_sub_distrib]
  have hdifference :
      (∑ j ∈ Finset.range h,
        ((if a ≤ j ∧ j < a+(n+1) then F j else 0) -
         (if a ≤ j ∧ j < a+n then F j else 0))) =
      (∑ j ∈ Finset.range h, if j = a+n then F j else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases heq : j = a+n
    · subst j
      have hnew : a ≤ a+n ∧ a+n < a+(n+1) := by omega
      have hold : ¬(a ≤ a+n ∧ a+n < a+n) := by omega
      simp [hnew, hold]
    · by_cases hold : a ≤ j ∧ j < a+n
      · have hnew : a ≤ j ∧ j < a+(n+1) := by omega
        simp [heq, hnew, hold]
      · have hnew : ¬(a ≤ j ∧ j < a+(n+1)) := by omega
        simp [heq, hnew, hold]
  rw [hdifference]
  have hguar : a+n < a+g ↔ n < g := by omega
  by_cases hterm : a+n < h
  · simp [Finset.sum_ite_eq, Finset.mem_range, hterm, F, hguar]
  · simp [Finset.sum_ite_eq, Finset.mem_range, hterm]
