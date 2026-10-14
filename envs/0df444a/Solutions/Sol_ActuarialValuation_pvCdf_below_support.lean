-- Prove2me | solution 1 for ActuarialValuation.pvCdf_below_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:58:48.300367+00:00
-- url     : https://prove2.me/submissions/1ebf1215-cd88-4698-a3fc-44f58b22f4a4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvCdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hmin : ∀ i, z < loss i) : pvCdf p loss z = 0 := by
  unfold pvCdf
  have h : ∀ i : Fin n, ¬ loss i ≤ z := by
    intro i
    exact not_le.mpr (hmin i)
  simp [h]
