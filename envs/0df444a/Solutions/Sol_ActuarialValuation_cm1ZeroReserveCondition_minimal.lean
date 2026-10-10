-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveCondition_minimal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:28:03.912827+00:00
-- url     : https://prove2.me/submissions/948ec1e8-70c4-41f1-a191-e37d355a3d82

import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ReserveYearProfit
import Definitions.Def_actuarial_cm1ZeroReserveCondition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R Q : ℕ → ℝ) (N t : ℕ)
  (hR : cm1ZeroReserveCondition c s g R N)
  (hg : ∀ j ∈ Finset.range N, 0 < g j)
  (hs : ∀ j ∈ Finset.range N, 0 ≤ s j)
  (hQend : Q N = 0)
  (hQpos : ∀ j, j ≤ N → 0 ≤ Q j)
  (hQprof : ∀ j ∈ Finset.range N, 0 ≤ cm1ReserveYearProfit c s g Q j)
  (ht : t ≤ N) : R t ≤ Q t := by
  have aux : ∀ k : ℕ, ∀ j : ℕ, N - j = k → j ≤ N → R j ≤ Q j := by
    intro k
    induction k with
    | zero =>
      intro j hsub hj
      have hlast : j = N := by omega
      subst j
      rw [hR.1, hQend]
    | succ k ih =>
      intro j hsub hj
      have hjlt : j < N := by omega
      have hnext : N - (j+1) = k := by omega
      have hle : j+1 ≤ N := by omega
      have hprev : R (j+1) ≤ Q (j+1) := ih (j+1) hnext hle
      have hRstep := hR.2 j (Finset.mem_range.mpr hjlt)
      have hgpos : 0 < g j := hg j (Finset.mem_range.mpr hjlt)
      have hspos : 0 ≤ s j := hs j (Finset.mem_range.mpr hjlt)
      have hqpr := hQprof j (Finset.mem_range.mpr hjlt)
      have hm : s j * R (j+1) ≤ s j * Q (j+1) :=
        mul_le_mul_of_nonneg_left hprev hspos
      rw [hRstep]
      unfold cm1ZeroReserveFloor
      apply max_le
      · exact hQpos j hj
      · apply (div_le_iff₀ hgpos).2
        unfold cm1ReserveYearProfit at hqpr
        nlinarith [hqpr, hm]
  exact aux (N - t) t rfl ht
