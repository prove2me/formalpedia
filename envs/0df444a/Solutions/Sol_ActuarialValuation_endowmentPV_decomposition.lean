-- Prove2me | solution 1 for ActuarialValuation.endowmentPV_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T06:14:01.812422+00:00
-- url     : https://prove2.me/submissions/456562a8-1b0d-401f-aa53-0c033830188b

import Mathlib
import Definitions.Def_actuarial_endowmentAssurancePV
import Definitions.Def_actuarial_curtatePureEndowmentPV
import Definitions.Def_actuarial_curtateSurvivalEvent
import Definitions.Def_actuarial_termAssurancePV
import Definitions.Def_actuarial_deathYearEvent
import Theorems.Thm_ActuarialValuation_termAssurancePV_eq_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n : ℕ)
    (ω : Ω)
    : endowmentAssurancePV K v n ω = termAssurancePV K v n ω + curtatePureEndowmentPV K v n ω := by
  classical
  have hsum :
      termAssurancePV K v n ω =
        ∑ k ∈ Finset.range n, if K ω = k then v ^ (k + 1) else 0 := by
    rw [termAssurancePV_eq_sum K v n ω]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases heq : K ω = k
    · simp [deathYearEvent, Set.indicator, heq]
    · simp [deathYearEvent, Set.indicator, heq]
  rw [hsum]
  by_cases hlt : K ω < n
  · have hle : K ω + 1 ≤ n := Nat.succ_le_iff.mpr hlt
    have hpay :
        (∑ k ∈ Finset.range n, if K ω = k then v ^ (k + 1) else 0) =
          v ^ (K ω + 1) := by
      rw [Finset.sum_eq_single (K ω)]
      · simp [Finset.mem_range.mpr hlt]
      · intro j hj hneq
        simp [hneq.symm]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr hlt))
    have hmin : min (K ω + 1) n = K ω + 1 := min_eq_left hle
    have hnosurv : ¬ n ≤ K ω := Nat.not_le_of_gt hlt
    simp [endowmentAssurancePV, hmin, curtatePureEndowmentPV,
          curtateSurvivalEvent, Set.indicator, hnosurv, hpay]
  · have hsurv : n ≤ K ω := Nat.le_of_not_gt hlt
    have hpay :
        (∑ k ∈ Finset.range n, if K ω = k then v ^ (k + 1) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hneq : K ω ≠ k := by omega
      simp [hneq]
    have hmin : min (K ω + 1) n = n := min_eq_right (by omega)
    simp [endowmentAssurancePV, hmin, curtatePureEndowmentPV,
          curtateSurvivalEvent, Set.indicator, hsurv, hpay]

