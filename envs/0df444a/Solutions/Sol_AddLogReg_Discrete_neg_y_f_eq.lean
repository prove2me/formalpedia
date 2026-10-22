-- Prove2me | solution 1 for AddLogReg.Discrete.neg_y_f_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:27:25.410616+00:00
-- url     : https://prove2.me/submissions/d3cb212e-3d5c-4908-8e0c-bc2fc6175206

import Mathlib
import Definitions.Def_AddLogReg_Discrete_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem solution (y s : ℝ) (hy : y = 1 ∨ y = -1) (hs : s = 1 ∨ s = -1) :
    -(y * s) = 2 * (if y ≠ s then 1 else 0) - 1 ∧
      ∀ c : ℝ, Real.exp (-(c * s * y)) =
        Real.exp (-c) * Real.exp (2 * c * (if y ≠ s then 1 else 0)) := by
  have key : -(y * s) = 2 * (if y ≠ s then (1:ℝ) else 0) - 1 := by
    rcases hy with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num
  refine ⟨key, fun c => ?_⟩
  rw [← Real.exp_add]
  congr 1
  have : c * s * y = c * (y * s) := by ring
  rw [this]
  have h2 : -(c * (y * s)) = c * (-(y * s)) := by ring
  rw [h2, key]; ring
