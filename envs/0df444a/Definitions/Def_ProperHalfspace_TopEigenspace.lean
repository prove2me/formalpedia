-- Prove2me | Definitions.Def_ProperHalfspace_TopEigenspace
-- name    : ProperHalfspace_TopEigenspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:56.375842+00:00
-- url     : https://prove2.me/theorems/27113d86-b2bf-4cec-a000-1cc2fe4e5153
-- title:
--   The top eigenspace $\mathrm{Eigen}_\lambda(M)$, the quadratic form and the operator norm
-- statement:
--   For a symmetric positive semidefinite matrix $M$ and $\lambda>0$, $\mathrm{Eigen}_\lambda(M)$ is the span of the eigenvectors of $M$ with eigenvalue at least $\lambda$. This module also fixes the quadratic form $v^\top Mv$ and the $\ell_2$ operator norm $\|A\|_{\mathrm{op}}$.
--
--   **Formalization Note** All three are generic in the finite index type, because the paper applies them to principal submatrices $M[T,T]$. $\|\cdot\|_{\mathrm{op}}$ is the norm of `Matrix.toEuclideanCLM`, not Mathlib's default matrix norm. The eigenspace is a supremum of `Module.End.eigenspace` over eigenvalues $\mu\ge\lambda$.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Definition 14, p.20

import Mathlib

namespace ProperHalfspace

/-!
# Top eigenspaces, quadratic forms and the operator norm

De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026), Definition 14, p.20.

**Formalization Note.** Everything is generic in the index type, because the paper applies it to principal submatrices
`M[T, T]`. `opNorm` is the `ℓ₂ → ℓ₂` operator norm, not Mathlib's default matrix norm.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Definition 14: `Eigen_λ(M)`, the span of the eigenvectors of `M` with eigenvalue at least `λ`. -/
noncomputable def topEigenspace (M : Matrix ι ι ℝ) (lam : ℝ) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  ⨆ μ : {μ : ℝ // lam ≤ μ}, Module.End.eigenspace (Matrix.toEuclideanLin M) μ

/-- The quadratic form `v^⊤ M v`. -/
noncomputable def quadForm (M : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ j, v i * M i j * v j

/-- The `ℓ₂` operator norm `‖A‖_op`. -/
noncomputable def opNorm (A : Matrix ι ι ℝ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) A‖

end ProperHalfspace


