-- Prove2me | Definitions.Def_ModernConvex_MatrixVec
-- name    : ModernConvex_MatrixVec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:39:13.410283+00:00
-- url     : https://prove2.me/theorems/fbf61289-cf91-4e0a-bead-d9be8f0193aa
-- title:
--   Matrices as vectors of length $n^2$: the Frobenius-pairing reindexing
-- statement:
--   **Matrices as vectors.** For an $n\times n$ real matrix $A$, `vecFin A` is the vector of length $n^2$ listing the entries column by column, and `finToMat` is its inverse. The point of the enumeration is the identity
--   $$\texttt{vecFin}\,A\cdot\texttt{vecFin}\,B=\sum_{i,j}A_{ij}B_{ij}$$
--   for symmetric $A,B$ — the coordinate dot product on $\mathbb R^{n^2}$ is the Frobenius (trace) pairing on matrices. This is what allows an ellipsoid method formulated on $\mathbb R^m$ with the coordinate dot product to be run on a body of matrices, such as $\{X\succeq0,\ X_{ii}=1\}$.
--
--   The file also records that `vecFin` is additive, and that $vv^{\mathsf T}$ (with a sign) is symmetric, which is the shape of the separating matrices the oracle emits.
-- source:
--   Reindexing used to apply Bubeck, arXiv:1405.4980v2, Thm 2.4 (stated on R^m with the coordinate dot product) to the matrix body of the MAXCUT SDP of Ben-Tal-Nemirovski, (4.3.15), p. 170.

import Mathlib

/-!
# Matrices as vectors of length `n * n`

The column-by-column enumeration of an `n × n` matrix as a vector of length `n * n`, and its
inverse. It is the reindexing under which the coordinate dot product of two enumerated vectors is
the Frobenius pairing of the matrices, which is what lets an ellipsoid method stated on
`Fin m → ℝ` run on a body of matrices.
-/

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- The column-by-column enumeration of an `n × n` matrix as a vector of length `n * n`. -/
noncomputable def vecFin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Fin (n * n) → ℝ :=
  fun k => Matrix.vec A (finProdFinEquiv.symm k)

/-- The inverse enumeration. -/
noncomputable def finToMat {n : ℕ} (x : Fin (n * n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => x (finProdFinEquiv (j, i))

@[simp] theorem finToMat_vecFin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    finToMat (vecFin A) = A := by
  ext i j
  simp [finToMat, vecFin]

@[simp] theorem vecFin_finToMat {n : ℕ} (x : Fin (n * n) → ℝ) : vecFin (finToMat x) = x := by
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  simp [finToMat, vecFin]

theorem vecFin_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    vecFin (A - B) = vecFin A - vecFin B := by
  funext k
  simp [vecFin, Matrix.sub_apply]

/-- The matrix with entries `-(v i * v j)` is symmetric. -/
theorem isHermitian_neg_mul {n : ℕ} (v : Fin n → ℝ) :
    (Matrix.of fun i j => -(v i * v j)).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, mul_comm]

end ModernConvex.Relaxations


