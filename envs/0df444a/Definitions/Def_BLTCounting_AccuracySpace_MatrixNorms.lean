-- Prove2me | Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms
-- name    : BLTCounting_AccuracySpace_MatrixNorms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:28.103542+00:00
-- url     : https://prove2.me/theorems/006ea1ea-d0bd-42b8-b308-e27a434c0d47
-- title:
--   Spectral and Frobenius norms, singular values, sorted eigenvalues, Rayleigh quotients, row and column sums
-- statement:
--   Let $A\in\mathbb C^{m\times n}$ be a complex matrix with row and column index types of any finite size. This module fixes the matrix quantities of the paper's Section 2.1.
--
--   1. The **spectral norm** $\|A\|_2$ is the operator norm of $x\mapsto Ax$ between Euclidean spaces; it equals the largest singular value $s_1(A)$.
--   2. The **singular values** $s_1(A)\ge s_2(A)\ge\dots\ge0$ are the square roots of the eigenvalues of $A^*A$. The count $\#\{j:s_j(A)>\tau\}$ runs over the $\min(m,n)$ singular values.
--   3. The **Frobenius norm** is $\|A\|_F=\bigl(\sum_{i,j}|A[i,j]|^2\bigr)^{1/2}$.
--   4. The induced norms are $\|B\|_1=\max_j\sum_i|B[i,j]|$ and $\|B\|_\infty=\max_i\sum_j|B[i,j]|$.
--   5. For Hermitian $A$, the eigenvalues are listed as $\lambda_1(A)\ge\lambda_2(A)\ge\dots$, with the counts $\#\{j:\lambda_j(A)>\tau\}$ and $\#\{j:\lambda_j(A)\ge\tau\}$ taken with multiplicity, and the **Rayleigh quotient** of $u\neq0$ is $u^*Au/\|u\|_2^2$.
--
--   These are the shared spectral objects used by every matrix statement of the mission.
--
--   **Formalization Note.** `singularValue` and `eigAt` are zero-indexed, so `singularValue A j` is $s_{j+1}(A)$ and `eigAt hA j` is $\lambda_{j+1}(A)$. Both return $0$ beyond the available indices. The singular values are Mathlib's `LinearMap.singularValues`. On an empty index type `maxColSum` and `maxRowSum` are $0$.
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Section 2.1, printed p. 10 (PDF p. 11); Claim 6.1, printed p. 34 (PDF p. 35)

import Mathlib

open Matrix

namespace BLTCounting.AccuracySpace

section Rectangular

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The spectral norm `‖A‖₂` of a complex matrix `A ∈ ℂ^{m×n}` (Henzinger–Upadhyay, §2.1, PDF p. 11):
the operator norm of `x ↦ Ax` from Euclidean `ℂⁿ` to Euclidean `ℂᵐ`, which equals `s₁(A)`. -/
noncomputable def specNorm (A : Matrix m n ℂ) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

/-- The zero-indexed, zero-extended singular values of `A`, in nonincreasing order:
`singularValue A j` is the source's `s_{j+1}(A)` (§2.1, PDF p. 11) for `j < min(m, n)`, and `0`
for larger `j`. This is Mathlib's `LinearMap.singularValues` of `x ↦ Ax`. -/
noncomputable def singularValue (A : Matrix m n ℂ) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j

/-- The count `#{j : s_j(A) > τ}`, with `j` running over the source's `min(m, n)` singular values
(Theorem 2.3, PDF p. 11). -/
noncomputable def singularCountAbove (A : Matrix m n ℂ) (τ : ℝ) : ℕ :=
  ((Finset.range (min (Fintype.card m) (Fintype.card n))).filter
    (fun j => τ < singularValue A j)).card

end Rectangular

section Entrywise

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The Frobenius norm `‖A‖_F = (∑_{i,j} |A[i,j]|²)^{1/2}` (§2.1, PDF p. 11). -/
noncomputable def frobNorm (A : Matrix m n ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2)

/-- The maximum absolute column sum `‖B‖₁ = max_j ∑_i |B[i,j]|` (Claim 6.1, PDF p. 35). The supremum
is over a finite index type; it is `0` when there are no columns. -/
noncomputable def maxColSum (B : Matrix m n ℂ) : ℝ :=
  ⨆ j, ∑ i, ‖B i j‖

/-- The maximum absolute row sum `‖B‖_∞ = max_i ∑_j |B[i,j]|` (Claim 6.1, PDF p. 35). The supremum
is over a finite index type; it is `0` when there are no rows. -/
noncomputable def maxRowSum (B : Matrix m n ℂ) : ℝ :=
  ⨆ i, ∑ j, ‖B i j‖

end Entrywise

section Hermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The zero-indexed eigenvalues of a Hermitian matrix in nonincreasing order: `eigAt hA j` is the
source's `λ_{j+1}(A)` (§2.1, PDF p. 11) for `j < card n`, and `0` beyond the dimension. -/
noncomputable def eigAt {A : Matrix n n ℂ} (hA : A.IsHermitian) (j : ℕ) : ℝ :=
  if h : j < Fintype.card n then hA.eigenvalues₀ ⟨j, h⟩ else 0

/-- The count `#{j : λ_j(A) > τ}`, with multiplicity, of a Hermitian matrix. -/
noncomputable def eigCountAbove {A : Matrix n n ℂ} (hA : A.IsHermitian) (τ : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : n => τ < hA.eigenvalues i)).card

/-- The count `#{j : λ_j(A) ≥ τ}`, with multiplicity, of a Hermitian matrix. -/
noncomputable def eigCountAtLeast {A : Matrix n n ℂ} (hA : A.IsHermitian) (τ : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : n => τ ≤ hA.eigenvalues i)).card

/-- The squared Euclidean norm `‖u‖₂² = ∑_i |u[i]|²` of a complex vector. -/
noncomputable def euclSq (u : n → ℂ) : ℝ :=
  ∑ i, ‖u i‖ ^ 2

/-- The Rayleigh quotient `u* A u / ‖u‖₂²`. The numerator is the real part of `u* A u`, which is
already real when `A` is Hermitian. -/
noncomputable def rayleigh (A : Matrix n n ℂ) (u : n → ℂ) : ℝ :=
  (star u ⬝ᵥ (A *ᵥ u)).re / euclSq u

end Hermitian

end BLTCounting.AccuracySpace


