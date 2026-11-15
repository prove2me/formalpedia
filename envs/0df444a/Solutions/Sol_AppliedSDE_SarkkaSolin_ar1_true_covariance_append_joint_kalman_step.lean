-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ar1_true_covariance_append_joint_kalman_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:05:59.264196+00:00
-- url     : https://prove2.me/submissions/2846d7e3-7ed0-4054-9ee0-ef1df37ab5df

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_batch_covariance_fromBlocks_system
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_fromBlocks_last_covariance_system
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_kalman_joint_update
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_appended_batch_last_row_in_schur_coordinates
import Theorems.Thm_AppliedSDE_SarkkaSolin_ar1_cross_covariance_last_row_smul
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (a V r : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hV : 0 < V) (hr : 0 < r)
    (y : Fin (n + 2) -> ℝ) (Pold mold : ℝ) :
    let Cold : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      (Matrix.of fun i j => V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    let Cnew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      (Matrix.of fun i j => V * a ^ Nat.dist i.val j.val) +
        r • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    let Knew : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
      Matrix.of fun i j => V * a ^ Nat.dist i.val j.val
    let e : (Fin (n + 1) ⊕ Fin 1) ≃ Fin (n + 2) := finSumFinEquiv
    let kold : Fin (n + 1) -> ℝ :=
      fun i => V * a ^ Nat.dist n i.val
    let knew : Fin (n + 2) -> ℝ :=
      fun i => V * a ^ Nat.dist (n + 1) i.val
    let zM := Cnew⁻¹ |>.mulVec y
    let zV := Cnew⁻¹ |>.mulVec knew
    let pred : ℝ := a ^ 2 * Pold + V * (1 - a ^ 2)
    Cold⁻¹ * Cold = 1 ->
    Pold = V - (kold ⬝ᵥ (Cold⁻¹).mulVec kold) ->
    mold = kold ⬝ᵥ (Cold⁻¹).mulVec (fun i : Fin (n + 1) => y i.castSucc) ->
    (V + r) - ((a • kold) ⬝ᵥ (Cold⁻¹).mulVec (a • kold)) ≠ 0 ->
    ((Knew.mulVec zM) (Fin.last (n + 1)) =
      a * mold + pred / (pred + r) *
        (y (Fin.last (n + 1)) - a * mold)) ∧
    (V - (Knew.mulVec zV) (Fin.last (n + 1)) =
      pred * r / (pred + r)) := by
  intro Cold Cnew Knew e kold knew zM zV pred hAM hP hm hS
  let B : Matrix (Fin (n + 1)) (Fin 1) ℝ :=
    fun i _ => V * a ^ (n + 1 - i.val)
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V + r
  have hsys :=
    AppliedSDE.SarkkaSolin.ar1_batch_covariance_fromBlocks_system
      n a V r ha ha1 hV hr y
  change (Matrix.fromBlocks Cold B B.transpose D).mulVec (zM ∘ e) =
    y ∘ e at hsys
  have hY : y ∘ e =
      Sum.elim (fun i : Fin (n + 1) => y i.castSucc)
        (fun _ : Fin 1 => y (Fin.last (n + 1))) := by
    funext j
    rcases j with i | i
    · change y (e (Sum.inl i)) = y i.castSucc
      rw [finSumFinEquiv_apply_left]
      try rfl
    · fin_cases i
      change y (e (Sum.inr (0 : Fin 1))) = y (Fin.last (n + 1))
      rw [finSumFinEquiv_apply_right]
      try rfl
  have hBM : (Matrix.fromBlocks Cold B B.transpose D).mulVec (zM ∘ e) =
      Sum.elim (fun i : Fin (n + 1) => y i.castSucc)
        (fun _ : Fin 1 => y (Fin.last (n + 1))) := hsys.trans hY
  have hBV :=
    AppliedSDE.SarkkaSolin.ar1_fromBlocks_last_covariance_system
      n a V r ha ha1 hV hr
  change (Matrix.fromBlocks Cold B B.transpose D).mulVec (zV ∘ e) =
      Sum.elim (a • kold) (fun _ : Fin 1 => V) at hBV
  have hB : B = (fun i (_ : Fin 1) => (a • kold) i) := by
    ext i j
    change V * a ^ (n + 1 - i.val) = a * (V * a ^ Nat.dist n i.val)
    exact congrFun
      (AppliedSDE.SarkkaSolin.ar1_cross_covariance_last_row_smul
        n a V) i
  rw [hB] at hBM hBV
  have hj :=
    AppliedSDE.SarkkaSolin.schur_block_kalman_joint_update
      (n + 1) Cold (Cold⁻¹) hAM
      kold (fun i : Fin (n + 1) => y i.castSucc)
      a V r Pold mold (y (Fin.last (n + 1)))
      hP hm (zM ∘ e) (zV ∘ e) hBM hBV hS
  dsimp at hj
  rcases hj with ⟨hjM, hjV⟩
  have hrowM :=
    AppliedSDE.SarkkaSolin.ar1_appended_batch_last_row_in_schur_coordinates
      n a V zM
  have hrowV :=
    AppliedSDE.SarkkaSolin.ar1_appended_batch_last_row_in_schur_coordinates
      n a V zV
  change (Knew.mulVec zM) (Fin.last (n + 1)) =
    ((a • kold) ⬝ᵥ ((zM ∘ e) ∘ Sum.inl)) +
      V * (zM ∘ e) (Sum.inr (0 : Fin 1)) at hrowM
  change (Knew.mulVec zV) (Fin.last (n + 1)) =
    ((a • kold) ⬝ᵥ ((zV ∘ e) ∘ Sum.inl)) +
      V * (zV ∘ e) (Sum.inr (0 : Fin 1)) at hrowV
  constructor
  · rw [hrowM]
    exact hjM
  · rw [hrowV]
    exact hjV
