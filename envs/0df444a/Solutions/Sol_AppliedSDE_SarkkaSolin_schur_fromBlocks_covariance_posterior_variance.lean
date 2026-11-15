-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_fromBlocks_covariance_posterior_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:52:11.076819+00:00
-- url     : https://prove2.me/submissions/d7e004e0-00b3-4c12-8cb2-586dfcf869c2

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
    (z : Fin n ⊕ Fin 1 -> ℝ)
    (hAM : A * M = 1)
    (hblock :
      (Matrix.fromBlocks M
        (fun i (_ : Fin 1) => b i )
        (fun (_ : Fin 1) j => b j )
        (fun (_ _ : Fin 1) => V + r )).mulVec z =
        Sum.elim b (fun _ : Fin 1 => V))
    (hS : (V + r) - (b ⬝ᵥ A.mulVec b) ≠ 0) :
    V - ((b ⬝ᵥ (z ∘ Sum.inl)) + V * z (Sum.inr (0 : Fin 1))) =
      (V - (b ⬝ᵥ A.mulVec b)) * r /
        ((V + r) - (b ⬝ᵥ A.mulVec b)) := by
  classical
  let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => b i
  let C : Matrix (Fin 1) (Fin n) ℝ := fun _ j => b j
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => V + r
  have hblock' : (Matrix.fromBlocks M B C D).mulVec z = Sum.elim b (fun _ : Fin 1 => V) := hblock
  rw [Matrix.fromBlocks_mulVec] at hblock'
  have hrightComponent :
      C.mulVec (z ∘ Sum.inl) + D.mulVec (z ∘ Sum.inr) =
        fun _ : Fin 1 => V := by
    funext i
    simpa [Function.comp_def] using congrFun hblock' (Sum.inr i)
  have hC : (C.mulVec (z ∘ Sum.inl)) (0 : Fin 1) =
      b ⬝ᵥ (z ∘ Sum.inl) := by
    rfl
  have hD : (D.mulVec (z ∘ Sum.inr)) (0 : Fin 1) =
      (V + r) * z (Sum.inr (0 : Fin 1)) := by
    simp [D, Matrix.mulVec, dotProduct]
  have hrow :
      (b ⬝ᵥ (z ∘ Sum.inl)) +
        (V + r) * z (Sum.inr (0 : Fin 1)) = V := by
    have h := congrFun hrightComponent (0 : Fin 1)
    simpa only [Pi.add_apply, hC, hD, Function.comp_apply] using h
  have hlast :=
    AppliedSDE.SarkkaSolin.schur_fromBlocks_last_coordinate
      n M A b (V + r) (Sum.elim b (fun _ : Fin 1 => V))
      z hAM hblock hS
  have hlastEq :
      z (Sum.inr (0 : Fin 1)) =
        (V - (b ⬝ᵥ A.mulVec b)) /
        ((V + r) - (b ⬝ᵥ A.mulVec b)) := by
    simpa [Function.comp_def] using hlast
  calc
    V - ((b ⬝ᵥ (z ∘ Sum.inl)) +
        V * z (Sum.inr (0 : Fin 1))) =
      r * z (Sum.inr (0 : Fin 1)) := by nlinarith [hrow]
    _ = r * ((V - (b ⬝ᵥ A.mulVec b)) /
        ((V + r) - (b ⬝ᵥ A.mulVec b))) := by rw [hlastEq]
    _ = (V - (b ⬝ᵥ A.mulVec b)) * r /
        ((V + r) - (b ⬝ᵥ A.mulVec b)) := by ring
