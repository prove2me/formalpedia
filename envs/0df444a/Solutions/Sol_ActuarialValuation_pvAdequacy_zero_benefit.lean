-- Prove2me | solution 1 for ActuarialValuation.pvAdequacy_zero_benefit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:59:12.099955+00:00
-- url     : https://prove2.me/submissions/81b308a3-0712-4f3b-8989-d8518a29fc91

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvAdequacy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p annuity : Fin n → ℝ) (premium : ℝ) (hprem : 0 ≤ premium) (ha : ∀ i, 0 ≤ annuity i) : pvAdequacy p (fun _ => 0) annuity premium = ∑ i : Fin n, p i := by
  unfold pvAdequacy
  apply Finset.sum_congr rfl
  intro i hi
  have h : (0:ℝ) ≤ premium * annuity i :=
    mul_nonneg hprem (ha i)
  simp [h]
