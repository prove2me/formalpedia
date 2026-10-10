-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonCountWeight_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:18:05.057458+00:00
-- url     : https://prove2.me/submissions/3b183608-f530-4350-a0a9-b93399d324b0

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_actuarial_compoundPoissonCountWeight

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate : ℝ) (m : ℕ) :
  (m + 1 : ℝ) * compoundPoissonCountWeight rate (m + 1) =
    rate * compoundPoissonCountWeight rate m := by
  unfold compoundPoissonCountWeight
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have hfac : (Nat.factorial m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp
