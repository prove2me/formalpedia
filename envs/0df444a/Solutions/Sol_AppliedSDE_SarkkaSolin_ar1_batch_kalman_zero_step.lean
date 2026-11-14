-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_batch_kalman_zero_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:17:48.649512+00:00
-- url     : https://prove2.me/submissions/a5179533-d1ba-499a-922e-df3a2424f0f0

import Mathlib
set_option autoImplicit false
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
open Matrix

theorem solution
    (V r : ℝ) (hV : 0 < V) (hr : 0 < r)
    (y : Fin 1 → ℝ) :
    let K : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V
    (K.mulVec (((K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec y)) 0 =
      V / (V + r) * y 0 := by
  let K : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V
  let M : Matrix (Fin 1) (Fin 1) ℝ :=
    K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ)
  let x : Fin 1 → ℝ := M⁻¹ *ᵥ y
  have hvr : 0 < V + r := add_pos hV hr
  have hvne : V + r ≠ 0 := ne_of_gt hvr
  have h00 : M 0 0 = V + r := by
    change V + r * (1 : ℝ) = V + r
    ring
  have hdet : M.det = V + r := by
    rw [Matrix.det_fin_one]
    exact h00
  have hunit : IsUnit M.det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr hvne
  have hmul : M *ᵥ x = y := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit,
      Matrix.one_mulVec]
  have hentry : (M *ᵥ x) 0 = (V + r) * x 0 := by
    calc
      (M *ᵥ x) 0 = M 0 0 * x 0 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      _ = (V + r) * x 0 := by rw [h00]
  have hcoord : (V + r) * x 0 = y 0 := by
    rw [← hentry]
    exact congrFun hmul 0
  have hx : x 0 = y 0 / (V + r) := by
    apply (eq_div_iff hvne).mpr
    simpa [mul_comm] using hcoord
  have hK : (K *ᵥ x) 0 = V * x 0 := by
    simp [Matrix.mulVec, dotProduct, K]
  change (K *ᵥ x) 0 = V / (V + r) * y 0
  rw [hK, hx]
  field_simp [hvne]