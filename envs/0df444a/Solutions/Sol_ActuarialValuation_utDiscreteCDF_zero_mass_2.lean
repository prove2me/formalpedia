-- Prove2me | solution 2 for ActuarialValuation.utDiscreteCDF_zero_mass
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T09:42:41.77107+00:00
-- url     : https://prove2.me/submissions/b0fa9f87-d48a-46ed-85b7-aa03e2afc27b

import Mathlib
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utDiscreteCDF

open ActuarialValuation

theorem solution {n : ℕ} (p : Fin n → ℝ) (x : Fin n → ℝ) (t : ℝ) (h : ∀ k, t<x k) : utDiscreteCDF p x t=0 := by
  unfold utDiscreteCDF
  apply Finset.sum_eq_zero
  intro k
  have hk : ¬ x k ≤ t := not_le_of_gt (h k)
  simp [hk]

