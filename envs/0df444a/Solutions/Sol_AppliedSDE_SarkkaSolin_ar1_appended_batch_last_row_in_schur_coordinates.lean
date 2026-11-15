-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_appended_batch_last_row_in_schur_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:57:47.715243+00:00
-- url     : https://prove2.me/submissions/cc1d8690-4713-4861-bf4b-638b8daa7979

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_appended_covariance_last_row
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_cross_covariance_last_row_smul
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (a V : ℝ) (z : Fin (n + 2) -> ℝ) :
    let e : (Fin (n + 1) ⊕ Fin 1) ≃ Fin (n + 2) := finSumFinEquiv
    let K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let kold : Fin (n + 1) -> ℝ :=
      fun i => V * a ^ Nat.dist n i.val
    (K.mulVec z) (Fin.last (n + 1)) =
      ((a • kold) ⬝ᵥ ((z ∘ e) ∘ Sum.inl)) +
        V * (z ∘ e) (Sum.inr (0 : Fin 1)) := by
  intro e K kold
  have hrow :=
    AppliedSDE.SarkkaSolin.ar1_appended_covariance_last_row n a V z
  have hcross :=
    AppliedSDE.SarkkaSolin.ar1_cross_covariance_last_row_smul n a V
  change (K.mulVec z) (Fin.last (n + 1)) =
    (fun i : Fin (n + 1) => V * a ^ (n + 1 - i.val))
      ⬝ᵥ (fun i => z i.castSucc) +
    V * z (Fin.last (n + 1)) at hrow
  rw [hcross] at hrow
  have hprefix : ((z ∘ e) ∘ Sum.inl) =
      (fun i : Fin (n + 1) => z i.castSucc) := by
    funext i
    change z (e (Sum.inl i)) = z i.castSucc
    rw [finSumFinEquiv_apply_left]
    try rfl
  have hlast : (z ∘ e) (Sum.inr (0 : Fin 1)) =
      z (Fin.last (n + 1)) := by
    change z (e (Sum.inr (0 : Fin 1))) = z (Fin.last (n + 1))
    rw [finSumFinEquiv_apply_right]
    try rfl
  rw [hprefix, hlast]
  exact hrow
