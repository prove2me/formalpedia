-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_schur_predicted_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:56:13.060171+00:00
-- url     : https://prove2.me/submissions/a4c06e22-c539-4223-a6fc-e99942b30d0b

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped Matrix

theorem solution
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ) (a V P : ℝ)
    (hP : P = V - (k ⬝ᵥ A.mulVec k)) :
    V - ((a • k) ⬝ᵥ A.mulVec (a • k)) =
      a ^ 2 * P + V * (1 - a ^ 2) := by
  have hlin : A.mulVec (a • k) = a • A.mulVec k := by
    simpa only [Matrix.mulVecLin_apply] using (A.mulVecLin).map_smul a k
  have hquadratic :
      ((a • k) ⬝ᵥ A.mulVec (a • k)) =
        a ^ 2 * (k ⬝ᵥ A.mulVec k) := by
    rw [hlin]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [hquadratic, hP]
  ring
