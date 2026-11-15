-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_fromBlocks_covariance_posterior_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:52:19.722199+00:00
-- url     : https://prove2.me/submissions/264b0df4-3fc0-42b7-b4c3-7e7d83012f04

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_fromBlocks_last_coordinate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix
open scoped Matrix
set_option autoImplicit false
theorem solution
    (n : ℕ) (M A : Matrix (Fin n) (Fin n) ℝ)
    (b : Fin n -> ℝ) (V r : ℝ)
    (y z : Fin n ⊕ Fin 1 -> ℝ)
    (hAM : A * M = 1)
    (hblock :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => b i )
        (fun (_ : Fin 1) j => b j )
        (fun (_ _ : Fin 1) => V + r )).mulVec z = y)
    (hS : (V + r) - (b ⬝ᵥ A.mulVec b) ≠ 0) :
    (b ⬝ᵥ (z ∘ Sum.inl)) + V * z (Sum.inr (0 : Fin 1)) =
      y (Sum.inr (0 : Fin 1)) -
        r * ((y (Sum.inr (0 : Fin 1)) -
          (b ⬝ᵥ A.mulVec (y ∘ Sum.inl))) /
          ((V + r) - (b ⬝ᵥ A.mulVec b))) := by
  classical
  let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => b i
  let C : Matrix (Fin 1) (Fin n) ℝ := fun _ j => b j
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V + r
  have hblock' : (Matrix.fromBlocks M B C D).mulVec z = y := hblock
  rw [Matrix.fromBlocks_mulVec] at hblock'
  have hrightComponent :
      C.mulVec (z ∘ Sum.inl) + D.mulVec (z ∘ Sum.inr) =
        y ∘ Sum.inr := by
    funext i
    simpa using congrFun hblock' (Sum.inr i)
  have hC : (C.mulVec (z ∘ Sum.inl)) (0 : Fin 1) =
      b ⬝ᵥ (z ∘ Sum.inl) := by
    rfl
  have hD : (D.mulVec (z ∘ Sum.inr)) (0 : Fin 1) =
      (V + r) * z (Sum.inr (0 : Fin 1)) := by
    simp [D, Matrix.mulVec, dotProduct]
  have hrow :
      (b ⬝ᵥ (z ∘ Sum.inl)) +
        (V + r) * z (Sum.inr (0 : Fin 1)) = y (Sum.inr (0 : Fin 1)) := by
    have h := congrFun hrightComponent (0 : Fin 1)
    simpa only [Pi.add_apply, hC, hD, Function.comp_apply] using h
  have hlast :=
    AppliedSDE.SarkkaSolin.schur_fromBlocks_last_coordinate
      n M A b (V + r) y z hAM hblock hS
  calc
    (b ⬝ᵥ (z ∘ Sum.inl)) +
        V * z (Sum.inr (0 : Fin 1)) =
      y (Sum.inr (0 : Fin 1)) -
        r * z (Sum.inr (0 : Fin 1)) := by nlinarith [hrow]
    _ = y (Sum.inr (0 : Fin 1)) -
        r * ((y (Sum.inr (0 : Fin 1)) -
          (b ⬝ᵥ A.mulVec (y ∘ Sum.inl))) /
          ((V + r) - (b ⬝ᵥ A.mulVec b))) := by rw [hlast]
