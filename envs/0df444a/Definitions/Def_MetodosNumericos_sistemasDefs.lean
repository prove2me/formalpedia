-- Prove2me | Definitions.Def_MetodosNumericos_sistemasDefs
-- name    : MetodosNumericos_sistemasDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T16:34:50.433607+00:00
-- url     : https://prove2.me/theorems/57554fff-1c4e-4170-88bf-f5017647ca17
-- title:
--   Diagonal dominance, Jacobi and Gauss-Seidel iterations
-- statement:
--   Diagonal dominance of a square real matrix, the Jacobi sweep and its iterates, and the Gauss-Seidel sweep — defined through a partial sweep that updates coordinates one at a time in increasing order — and its iterates.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 5: §5.6 p. 109 (Jacobi), §5.8 p. 111 (Gauss-Seidel), §5.10 p. 113 (matrizes diagonalmente dominantes).

import Mathlib

namespace MetodosNumericos

open Finset

/-- A square matrix is *diagonally dominant* (diagonalmente dominante) when each
diagonal entry dominates, in absolute value, the sum of the absolute values of the
other entries of its row. -/
def DiagDominant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, |A i j| < |A i i|

/-- One sweep of the Jacobi method: every coordinate of the new vector is computed
from the *old* vector, `yᵢ = (bᵢ - ∑_{j ≠ i} aᵢⱼ xⱼ) / aᵢᵢ`. -/
noncomputable def jacobiSweep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => (b i - ∑ j ∈ Finset.univ.erase i, A i j * x j) / A i i

/-- The Jacobi iterates: `x⁽⁰⁾ = x₀` and `x⁽ᵏ⁺¹⁾` is one Jacobi sweep of `x⁽ᵏ⁾`. -/
noncomputable def jacobiSeq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x0 : Fin n → ℝ) :
    ℕ → (Fin n → ℝ)
  | 0 => x0
  | k + 1 => jacobiSweep A b (jacobiSeq A b x0 k)

/-- Auxiliary partial sweep of the Gauss-Seidel method: after `k` steps the first `k`
coordinates have already been overwritten with their new values, and those new values
are the ones used when the later coordinates are computed. -/
noncomputable def gsPartial {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    ℕ → (Fin n → ℝ)
  | 0 => x
  | k + 1 =>
      let y := gsPartial A b x k
      if h : k < n then
        Function.update y ⟨k, h⟩
          ((b ⟨k, h⟩ - ∑ j ∈ Finset.univ.erase (⟨k, h⟩ : Fin n), A ⟨k, h⟩ j * y j) /
            A ⟨k, h⟩ ⟨k, h⟩)
      else y

/-- One sweep of the Gauss-Seidel method: the coordinates are updated in order
`i = 0, 1, …, n-1`, each one using the already updated values of the previous
coordinates and the old values of the later ones. -/
noncomputable def gaussSeidelSweep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ) :
    Fin n → ℝ :=
  gsPartial A b x n

/-- The Gauss-Seidel iterates: `x⁽⁰⁾ = x₀` and `x⁽ᵏ⁺¹⁾` is one Gauss-Seidel sweep
of `x⁽ᵏ⁾`. -/
noncomputable def gaussSeidelSeq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x0 : Fin n → ℝ) :
    ℕ → (Fin n → ℝ)
  | 0 => x0
  | k + 1 => gaussSeidelSweep A b (gaussSeidelSeq A b x0 k)

end MetodosNumericos


