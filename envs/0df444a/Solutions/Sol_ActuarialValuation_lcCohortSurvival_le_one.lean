-- Prove2me | solution 1 for ActuarialValuation.lcCohortSurvival_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:25:44.508728+00:00
-- url     : https://prove2.me/submissions/0cd9b6f8-0564-462b-a778-875f28326a32

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcCohortSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (q : ℕ → ℝ) (n : ℕ)
    (hq : ∀ t ∈ Finset.range n, 0 ≤ q t ∧ q t ≤ 1) :
    lcCohortSurvival q n ≤ 1 := by
  have h : ∀ m : ℕ,
      (∀ t ∈ Finset.range m, 0 ≤ q t ∧ q t ≤ 1) →
      0 ≤ lcCohortSurvival q m ∧ lcCohortSurvival q m ≤ 1 := by
    intro m
    induction m with
    | zero =>
        intro _
        simp [lcCohortSurvival]
    | succ m ih =>
        intro hm
        have hprev : ∀ t ∈ Finset.range m, 0 ≤ q t ∧ q t ≤ 1 := by
          intro t ht
          exact hm t (Finset.mem_range.mpr
            (Nat.lt_trans (Finset.mem_range.mp ht) (Nat.lt_succ_self m)))
        have hm0 : 0 ≤ q m ∧ q m ≤ 1 :=
          hm m (Finset.mem_range.mpr (Nat.lt_succ_self m))
        have hfactor0 : 0 ≤ 1 - q m := sub_nonneg.mpr hm0.2
        have hfactor1 : 1 - q m ≤ 1 := sub_le_self 1 hm0.1
        obtain ⟨hp0, hp1⟩ := ih hprev
        have hs : lcCohortSurvival q (m+1) =
            lcCohortSurvival q m * (1-q m) := by
          simp [lcCohortSurvival, Finset.prod_range_succ]
        constructor
        · rw [hs]
          exact mul_nonneg hp0 hfactor0
        · rw [hs]
          calc
            lcCohortSurvival q m * (1-q m) ≤
                lcCohortSurvival q m * 1 :=
                  mul_le_mul_of_nonneg_left hfactor1 hp0
            _ = lcCohortSurvival q m := by simp
            _ ≤ 1 := hp1
  exact (h n hq).2
