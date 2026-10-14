-- Prove2me | solution 1 for ActuarialValuation.lcLeeCarterCohort_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:41:50.583362+00:00
-- url     : https://prove2.me/submissions/f4d45fe4-4b55-482e-9111-88113ca50198

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcRate
import Definitions.Def_actuarial_lcRateRatio
import Definitions.Def_actuarial_lcCohortSurvival
import Definitions.Def_actuarial_lcCohortLives
import Definitions.Def_actuarial_lcExpectedDeathCost
import Theorems.Thm_ActuarialValuation_lcRate_ratio_reconstruction
import Theorems.Thm_ActuarialValuation_lcCohortSurvival_nonneg
import Theorems.Thm_ActuarialValuation_lcCohortSurvival_succ
import Theorems.Thm_ActuarialValuation_lcCohortLives_nonneg
import Theorems.Thm_ActuarialValuation_lcExpectedDeathCost_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b k1 k2 initial benefit : ℝ)
    (q : ℕ → ℝ) (n : ℕ)
    (hi : 0 ≤ initial) (hb : 0 ≤ benefit)
    (hq : ∀ t ∈ Finset.range (n+1), 0 ≤ q t ∧ q t ≤ 1) :
    (lcRate a b k2 = lcRate a b k1 * lcRateRatio b k1 k2) ∧
    (0 < lcRate a b k2) ∧
    (0 ≤ lcCohortSurvival q (n+1)) ∧
    (lcCohortSurvival q (n+1) ≤ lcCohortSurvival q n) ∧
    (0 ≤ lcExpectedDeathCost (lcCohortLives initial q n) (q n) benefit) := by
  have hprev : ∀ t ∈ Finset.range n, q t ≤ 1 := by
    intro t ht
    exact (hq t (Finset.mem_range.mpr
      (Nat.lt_trans (Finset.mem_range.mp ht) (Nat.lt_succ_self n)))).2
  have hnow : 0 ≤ q n ∧ q n ≤ 1 :=
    hq n (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have hsurvprev : 0 ≤ lcCohortSurvival q n :=
    lcCohortSurvival_nonneg q n hprev
  have hsurvnext : 0 ≤ lcCohortSurvival q (n+1) :=
    lcCohortSurvival_nonneg q (n+1) (fun t ht => (hq t ht).2)
  have hlives : 0 ≤ lcCohortLives initial q n :=
    lcCohortLives_nonneg initial q n hi hsurvprev
  have hcost : 0 ≤ lcExpectedDeathCost (lcCohortLives initial q n) (q n) benefit :=
    lcExpectedDeathCost_nonneg (lcCohortLives initial q n) (q n)
      benefit hlives hnow.1 hb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact lcRate_ratio_reconstruction a b k1 k2
  · unfold lcRate
    exact Real.exp_pos _
  · exact hsurvnext
  · rw [lcCohortSurvival_succ]
    have hfactor : 1-q n ≤ 1 := sub_le_self 1 hnow.1
    calc
      lcCohortSurvival q n * (1-q n) ≤
          lcCohortSurvival q n * 1 :=
            mul_le_mul_of_nonneg_left hfactor hsurvprev
      _ = lcCohortSurvival q n := by simp
  · exact hcost
