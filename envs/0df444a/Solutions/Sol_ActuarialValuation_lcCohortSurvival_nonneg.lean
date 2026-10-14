-- Prove2me | solution 1 for ActuarialValuation.lcCohortSurvival_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:25:44.474847+00:00
-- url     : https://prove2.me/submissions/56d24851-f23a-4ae1-a940-9387771d7622

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : ℕ → ℝ) (n : ℕ)
    (hq : ∀ t ∈ Finset.range n, q t ≤ 1) :
    0 ≤ lcCohortSurvival q n := by
  have h : ∀ m : ℕ, (∀ t ∈ Finset.range m, q t ≤ 1) →
      0 ≤ lcCohortSurvival q m := by
    intro m
    induction m with
    | zero =>
        intro _
        simp [lcCohortSurvival]
    | succ m ih =>
        intro hm
        have hprev : ∀ t ∈ Finset.range m, q t ≤ 1 := by
          intro t ht
          exact hm t (Finset.mem_range.mpr
            (Nat.lt_trans (Finset.mem_range.mp ht) (Nat.lt_succ_self m)))
        have hfactor : 0 ≤ 1-q m :=
          sub_nonneg.mpr (hm m (Finset.mem_range.mpr (Nat.lt_succ_self m)))
        have hs : lcCohortSurvival q (m+1) =
            lcCohortSurvival q m * (1-q m) := by
          simp [lcCohortSurvival, Finset.prod_range_succ]
        rw [hs]
        exact mul_nonneg (ih hprev) hfactor
  exact h n hq
