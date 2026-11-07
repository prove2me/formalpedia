-- Prove2me | Definitions.Def_ModernConvex_SchurStep
-- name    : ModernConvex_SchurStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:45:28.88197+00:00
-- url     : https://prove2.me/theorems/94152c2d-f60b-4543-b6cf-f315785b1c9e
-- title:
--   The Schur complement at a pivot as a matrix on the complement index
-- statement:
--   **The Schur complement at a pivot, as a matrix.**
--
--   For a real matrix $M$ of order $n$ and an index $i$, `schurStep M i` is the matrix of order $n-1$ on the complement of $i$ with entries
--   $$(\texttt{schurStep}\ M\ i)_{jk}=M_{jk}-M_{ji}\,M_{ii}^{-1}\,M_{ik}\qquad(j,k\ne i),$$
--   i.e. the Schur complement $M_{\ne i,\ne i}-M_{\ne i,i}M_{ii}^{-1}M_{i,\ne i}$.
--
--   `extendAt i w` is the vector on all of $\{1,\dots,n\}$ obtained from $w$ by inserting $0$ at position $i$. It is the inverse correspondence used to move between the quadratic form of the Schur complement and the Schur form of $M$ at $i$: $Q_i(\texttt{extendAt}\ i\ w)=w^{\mathsf T}(\texttt{schurStep}\ M\ i)w$.
--
--   `schurStep_isHermitian` records that the Schur step of a symmetric matrix is symmetric, so the recursion can assume symmetry at every step. This is the data the well-founded recursion of the PSD oracle carries: the index type shrinks by one element per elimination.
-- source:
--   Schur complement / symmetric elimination at a 1x1 pivot; data structures for the recursive PSD oracle of the MAXCUT SDP separation problem (Bubeck arXiv:1405.4980v2, Thm 2.4).

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

/-!
# The Schur complement at a pivot, as a matrix

`schurForm M i` (see `ModernConvex_SchurForm`) is a quadratic form on the remaining coordinates.
To *iterate* the elimination the next step needs a matrix, so this file records the Schur
complement at a pivot as a matrix on the complement index type `{j // j ≠ i}`:

  `schurStep M i = fun j k => M j k - M j i * (M i i)⁻¹ * M i k`,

together with `extendAt`, the extension of a vector on the complement by zero at `i`. These are the
data the well-founded recursion of the PSD oracle carries: at each step the index type shrinks by
one element.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- The Schur complement of `M` at the pivot `i`, as a matrix on the complement of `i`. -/
noncomputable def schurStep {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Matrix {j : Fin n // j ≠ i} {j : Fin n // j ≠ i} ℝ :=
  fun j k => M j.1 k.1 - M j.1 i * (M i i)⁻¹ * M i k.1

/-- Extend a vector on the complement of `i` by zero at `i`. -/
def extendAt {n : ℕ} (i : Fin n) (w : {j : Fin n // j ≠ i} → ℝ) : Fin n → ℝ :=
  fun j => if h : j = i then 0 else w ⟨j, h⟩

@[simp] theorem extendAt_self {n : ℕ} (i : Fin n) (w : {j : Fin n // j ≠ i} → ℝ) :
    extendAt i w i = 0 := by
  simp [extendAt]

theorem extendAt_of_ne {n : ℕ} (i : Fin n) (w : {j : Fin n // j ≠ i} → ℝ)
    {j : Fin n} (hj : j ≠ i) : extendAt i w j = w ⟨j, hj⟩ := by
  simp [extendAt, hj]

/-- **The Schur step preserves symmetry.** -/
theorem schurStep_isHermitian {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) : (schurStep M i).IsHermitian := by
  have hsymm : ∀ j : Fin n, M j i = M i j := by
    intro j
    simpa using (hM.apply j i).symm
  ext j k
  simp only [schurStep, Matrix.conjTranspose_apply, star_trivial]
  have h1 : M ↑k ↑j = M ↑j ↑k := by
    simpa using (hM.apply k.1 j.1).symm
  rw [h1, hsymm k.1, hsymm j.1]
  ring

end ModernConvex.Relaxations


