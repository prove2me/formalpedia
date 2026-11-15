-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.schur_matrix_last_component
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:07:17.750082+00:00
-- url     : https://prove2.me/submissions/ae83fa53-335a-4671-864c-28f0df2bef03

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_schur_block_scalar_elimination
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix
open scoped Matrix

theorem solution
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (b u x : Fin n → ℝ) (w d v : ℝ)
    (hx : x = A.mulVec (u - w • b))
    (hrow : (b ⬝ᵥ x) + d * w = v)
    (hS : d - (b ⬝ᵥ A.mulVec b) ≠ 0) :
    w = (v - (b ⬝ᵥ A.mulVec u)) /
      (d - (b ⬝ᵥ A.mulVec b)) := by
  let M : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := A.mulVecLin
  let l : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ) b
  have hM : x = M (u - w • b) := by simpa [M] using hx
  have hl : l x + d * w = v := by simpa [l] using hrow
  have hs : d - l (M b) ≠ 0 := by simpa [l, M] using hS
  have h :=
    AppliedSDE.SarkkaSolin.schur_block_scalar_elimination
      n M l u b x w d v hM hl hs
  simpa [l, M] using h
