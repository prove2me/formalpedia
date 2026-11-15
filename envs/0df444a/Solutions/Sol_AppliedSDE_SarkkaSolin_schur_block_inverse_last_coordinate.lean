-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_block_inverse_last_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:30:49.563925+00:00
-- url     : https://prove2.me/submissions/8782c6a5-918e-438a-97e7-3971823287ad

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_matrix_last_component
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped Matrix

theorem solution
    (n : ℕ)
    (M A : Matrix (Fin n) (Fin n) ℝ)
    (hAM : A * M = 1)
    (k u z : Fin n → ℝ) (w d v : ℝ)
    (hleft : M.mulVec z + w • k = u)
    (hrow : (k ⬝ᵥ z) + d * w = v)
    (hS : d - (k ⬝ᵥ A.mulVec k) ≠ 0) :
    w = (v - (k ⬝ᵥ A.mulVec u)) /
      (d - (k ⬝ᵥ A.mulVec k)) := by
  have hInv : A.mulVec (M.mulVec z) = z := by
    rw [Matrix.mulVec_mulVec, hAM, Matrix.one_mulVec]
  have hleading : M.mulVec z = u - w • k :=
    (eq_sub_iff_add_eq).2 hleft
  have hz : z = A.mulVec (u - w • k) := by
    rw [← hleading]
    exact hInv.symm
  exact AppliedSDE.SarkkaSolin.schur_matrix_last_component
    n A k u z w d v hz hrow hS
