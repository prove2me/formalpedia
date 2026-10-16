-- Prove2me | solution 1 for ActuarialAnnuities.guarantee_marginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T06:13:24.822023+00:00
-- url     : https://prove2.me/submissions/cd2f3188-0df5-4797-a7ed-0daa928d2924

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bSurvivalPV
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAnnuities

theorem solution (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    bSurvivalPV h a n (g+1) delta v b p -
      bSurvivalPV h a n g delta v b p =
    if a+g < h ∧ a+g < a+n then
      b (a+g)*v^(a+g+delta)*
        (bSurvival h p a-bSurvival h p (a+g+delta))
    else 0 := by
  classical
  let F : ℕ → ℝ := fun j => b j * v^(j+delta)
  let S : ℝ := bSurvival h p a
  let T : ℕ → ℝ := fun j => bSurvival h p (j+delta)
  change (∑ j ∈ Finset.range h,
      if a ≤ j ∧ j < a+n then F j *
        (if j < a+(g+1) then S else T j) else 0) -
    (∑ j ∈ Finset.range h,
      if a ≤ j ∧ j < a+n then F j *
        (if j < a+g then S else T j) else 0) = _
  rw [← Finset.sum_sub_distrib]
  have hdifference :
      (∑ j ∈ Finset.range h,
        ((if a ≤ j ∧ j < a+n then F j *
             (if j < a+(g+1) then S else T j) else 0) -
         (if a ≤ j ∧ j < a+n then F j *
             (if j < a+g then S else T j) else 0))) =
      (∑ j ∈ Finset.range h,
        if j = a+g then
          (if a ≤ j ∧ j < a+n then F j*(S-T j) else 0)
        else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hpay : a ≤ j ∧ j < a+n
    · by_cases hlt : j < a+g
      · have hnew : j < a+(g+1) := by omega
        have hneq : j ≠ a+g := by omega
        simp [hpay, hlt, hnew, hneq]
      · by_cases heq : j = a+g
        · subst j
          have hnew : a+g < a+(g+1) := by omega
          simp [hpay, hlt, hnew, F, S, T]
          ring
        · have hnew : ¬j < a+(g+1) := by omega
          simp [hpay, hlt, hnew, heq]
    · simp [hpay]
  rw [hdifference]
  by_cases hh : a+g < h
  · by_cases hn : a+g < a+n
    · have ha : a ≤ a+g := by omega
      simp [Finset.sum_ite_eq, Finset.mem_range, hh, hn, ha, F, S, T]
    · simp [Finset.sum_ite_eq, Finset.mem_range, hh, hn, F, S, T]
  · simp [Finset.sum_ite_eq, Finset.mem_range, hh, F, S, T]
