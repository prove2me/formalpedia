-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveCondition_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:58.152183+00:00
-- url     : https://prove2.me/submissions/49af8987-8f5b-4700-8c48-351bb5dd92d5

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveCondition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R Q : ℕ → ℝ) (N t : ℕ) (hR : cm1ZeroReserveCondition c s g R N) (hQ : cm1ZeroReserveCondition c s g Q N) (ht : t ≤ N) : R t = Q t := by
  have aux : ∀ k : ℕ, ∀ j : ℕ, N - j = k → j ≤ N → R j = Q j := by
    intro k
    induction k with
    | zero =>
      intro j hsub hj
      have hlast : j = N := by omega
      subst j
      exact hR.1.trans hQ.1.symm
    | succ k ih =>
      intro j hsub hj
      have hjlt : j < N := by omega
      have hnext : N - (j+1) = k := by omega
      have hle : j+1 ≤ N := by omega
      have hprev : R (j+1) = Q (j+1) := ih (j+1) hnext hle
      calc
        R j = cm1ZeroReserveFloor (c j) (s j) (g j) (R (j+1)) :=
          hR.2 j (Finset.mem_range.mpr hjlt)
        _ = cm1ZeroReserveFloor (c j) (s j) (g j) (Q (j+1)) := by
          rw [hprev]
        _ = Q j := (hQ.2 j (Finset.mem_range.mpr hjlt)).symm
  exact aux (N - t) t rfl ht
