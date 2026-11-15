-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_fromBlocks_last_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:26:21.998204+00:00
-- url     : https://prove2.me/submissions/89ea08fb-07c4-4164-b38f-a78bdf241686

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_inverse_last_coordinate
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped Matrix

/-- The appended coordinate of a genuine 2-by-2 block matrix linear system
is the Schur complement quotient, with an explicit inverse of the old block. -/
theorem solution
    (n : ℕ) (M A : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n → ℝ) (d : ℝ)
    (y z : Fin n ⊕ Fin 1 → ℝ)
    (hAM : A * M = 1)
    (hblock :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => k i : Matrix (Fin n) (Fin 1) ℝ)
        (fun (_ : Fin 1) j => k j : Matrix (Fin 1) (Fin n) ℝ)
        (fun (_ _ : Fin 1) => d : Matrix (Fin 1) (Fin 1) ℝ)).mulVec z = y)
    (hS : d - (k ⬝ᵥ A.mulVec k) ≠ 0) :
    z (Sum.inr (0 : Fin 1)) =
      (y (Sum.inr (0 : Fin 1)) -
        (k ⬝ᵥ A.mulVec (y ∘ Sum.inl))) /
          (d - (k ⬝ᵥ A.mulVec k)) := by
  classical
  let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => k i
  let C : Matrix (Fin 1) (Fin n) ℝ := fun _ j => k j
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => d
  have hblock' : (Matrix.fromBlocks M B C D).mulVec z = y := hblock
  rw [Matrix.fromBlocks_mulVec] at hblock'
  have hleftComponent :
      M.mulVec (z ∘ Sum.inl) + B.mulVec (z ∘ Sum.inr) =
        y ∘ Sum.inl := by
    funext i
    simpa using congrFun hblock' (Sum.inl i)
  have hrightComponent :
      C.mulVec (z ∘ Sum.inl) + D.mulVec (z ∘ Sum.inr) =
        y ∘ Sum.inr := by
    funext i
    simpa using congrFun hblock' (Sum.inr i)
  have hB : B.mulVec (z ∘ Sum.inr) =
      z (Sum.inr (0 : Fin 1)) • k := by
    funext i
    simp [B, Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]
  have hC : (C.mulVec (z ∘ Sum.inl)) (0 : Fin 1) =
      k ⬝ᵥ (z ∘ Sum.inl) := by
    rfl
  have hD : (D.mulVec (z ∘ Sum.inr)) (0 : Fin 1) =
      d * z (Sum.inr (0 : Fin 1)) := by
    simp [D, Matrix.mulVec, dotProduct]
  have hleft :
      M.mulVec (z ∘ Sum.inl) + z (Sum.inr (0 : Fin 1)) • k =
        y ∘ Sum.inl := by
    simpa only [hB] using hleftComponent
  have hright : (k ⬝ᵥ (z ∘ Sum.inl)) +
      d * z (Sum.inr (0 : Fin 1)) =
        y (Sum.inr (0 : Fin 1)) := by
    have h := congrFun hrightComponent (0 : Fin 1)
    simpa only [Pi.add_apply, hC, hD, Function.comp_apply] using h
  exact AppliedSDE.SarkkaSolin.schur_block_inverse_last_coordinate
    n M A hAM k (y ∘ Sum.inl) (z ∘ Sum.inl)
      (z (Sum.inr 0)) d (y (Sum.inr 0)) hleft hright hS
