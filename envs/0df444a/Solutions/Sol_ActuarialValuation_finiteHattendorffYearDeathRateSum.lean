-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffYearDeathRateSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:57:14.925489+00:00
-- url     : https://prove2.me/submissions/fb414d80-c679-4664-8ba7-6602a31aae36

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_finiteMortalityDeathRate
import Definitions.Def_actuarial_finiteMortalityDeathMass
import Definitions.Def_actuarial_finiteMortalitySurvivalMass
import Definitions.Def_actuarial_finiteMortalitySurvivalRate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (K : Ω → ℕ) (t : ℕ)
    (hS : 0 < finiteMortalitySurvivalMass w K t) :
    finiteMortalityDeathRate w K t +
      finiteMortalitySurvivalRate w K t = 1 := by
  classical
  have hpoint (ω : Ω) :
      (if t ≤ K ω then w ω else 0) =
        (if K ω = t then w ω else 0) +
          (if t + 1 ≤ K ω then w ω else 0) := by
    by_cases heq : K ω = t
    · simp [heq]
    · by_cases hnext : t + 1 ≤ K ω
      · have hcur : t ≤ K ω :=
          le_trans (Nat.le_succ t) hnext
        simp [heq, hnext, hcur]
      · have hnot : ¬ t ≤ K ω := by
          intro hcur
          rcases eq_or_lt_of_le hcur with hEqual | hLess
          · exact heq hEqual.symm
          · exact hnext (Nat.succ_le_iff.mpr hLess)
        simp [heq, hnext, hnot]
  have hmass :
      finiteMortalitySurvivalMass w K t =
        finiteMortalityDeathMass w K t +
          finiteMortalitySurvivalMass w K (t + 1) := by
    unfold finiteMortalitySurvivalMass finiteMortalityDeathMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ω hω
    exact hpoint ω
  change
    finiteMortalityDeathMass w K t / finiteMortalitySurvivalMass w K t +
      finiteMortalitySurvivalMass w K (t + 1) / finiteMortalitySurvivalMass w K t = 1
  rw [← add_div, ← hmass]
  exact div_self (ne_of_gt hS)
