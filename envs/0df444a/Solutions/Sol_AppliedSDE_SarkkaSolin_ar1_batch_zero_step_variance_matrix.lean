-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_batch_zero_step_variance_matrix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:43:23.303234+00:00
-- url     : https://prove2.me/submissions/bbf62820-2162-435c-92d1-e063669ce2de

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_kalman_zero_step
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (V r : ℝ) (hV : 0 < V) (hr : 0 < r) :
    let K : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V
    let k : Fin 1 -> ℝ := fun _ => V
    V - (k ⬝ᵥ (((K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec k)) =
      V * r / (V + r) := by
  let K : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V
  let k : Fin 1 -> ℝ := fun _ => V
  have hmean :=
    AppliedSDE.SarkkaSolin.ar1_batch_kalman_zero_step V r hV hr k
  change (K.mulVec (((K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec k)) 0 =
    V / (V + r) * k 0 at hmean
  have hdot : (K.mulVec (((K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec k)) 0 =
      k ⬝ᵥ (((K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec k) := by
    rfl
  rw [hdot] at hmean
  change V - k ⬝ᵥ (((K + r • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹).mulVec k) =
    V * r / (V + r)
  rw [hmean]
  dsimp [k]
  have hvne : V + r ≠ 0 := ne_of_gt (add_pos hV hr)
  field_simp [hvne]
  ring
