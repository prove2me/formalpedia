-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gp_batch_posterior_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:56:35.536247+00:00
-- url     : https://prove2.me/submissions/6a664bae-5de5-4141-96e1-5b287492dded

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped BigOperators

theorem solution
    {n : ℕ}
    (K : Matrix (Fin n) (Fin n) ℝ)
    (r : ℝ) (y : Fin n → ℝ)
    (hM : (K + r • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef) :
    K.mulVec (((K + r • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec y) =
      y - r • (((K + r • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec y) := by
  let M : Matrix (Fin n) (Fin n) ℝ :=
    K + r • (1 : Matrix (Fin n) (Fin n) ℝ)
  let x : Fin n → ℝ := M⁻¹ *ᵥ y
  have hunit : IsUnit M := hM.isUnit
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hunit
  have hmul : M *ᵥ x = y := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet,
      Matrix.one_mulVec]
  have hlinear : K *ᵥ x + r • x = y := by
    calc
      K *ᵥ x + r • x =
        (K + r • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x := by
          simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = y := hmul
  change K *ᵥ x = y - r • x
  exact eq_sub_of_add_eq hlinear