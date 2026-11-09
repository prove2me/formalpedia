-- Prove2me | Definitions.Def_L22EigEst_highPart
-- name    : L22EigEst_highPart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:14:27.848522+00:00
-- url     : https://prove2.me/theorems/2837473e-e6e0-4e19-b761-96733b54c279
-- title:
--   Spectral split $A=A_H+A_L$ at threshold $\lambda$ (Definition 2.3), and the off-diagonal part
-- statement:
--   Let $A=U\Lambda U^\top$ be an eigendecomposition of a symmetric $A\in\mathbb R^{n\times n}$ with eigenvalues $\mu_1,\dots,\mu_n$. For a threshold $\lambda$,
--
--   $$A_H=U\,\mathrm{diag}\big(\mu_i\,\mathbf 1[|\mu_i|\ge\lambda]\big)\,U^\top,\qquad A_L=A-A_H,$$
--
--   so $A_H$ keeps the eigenpairs of magnitude at least $\lambda$ and $A_L$ those of magnitude smaller than $\lambda$ (Definition 2.3). $A_H$ is the sum of $\mu P_\mu$ over the distinct eigenvalues $\mu$ with $|\mu|\ge\lambda$, where $P_\mu$ is the orthogonal projector onto the eigenspace, so it does not depend on the eigenbasis.
--
--   The **off-diagonal part** of a square matrix $B$ is $B$ with its diagonal set to $0$; the paper writes $A'_L=D_L+H_L$ with $H_L$ the off-diagonal part of $A'_L$.
--
--   **Formalization Note** $U$ is Mathlib's orthonormal eigenvector matrix. The module proves that $A_H$ and $A_L$ are symmetric.
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Definition 2.3, pp.9–10; §4.3, p.16 (A′_L = D_L + H_L)

import Mathlib

namespace L22EigEst

/-- **The large-eigenvalue part `A_H`** of a symmetric matrix at threshold `λ`
(Definition 2.3, pp.9–10), Menand, Waingarten, STOC 2027 submission (manuscript sha256 b1f6adce…):
"A_H = U_H Λ_H U_H⊺ … The matrix U_H has columns given by the subset of eigenvectors from U whose
corresponding eigenvalue has magnitude at least λ."

**Formalization Note.** With `U` Mathlib's orthonormal eigenvector matrix
`hA.eigenvectorUnitary` and `μ = hA.eigenvalues`, `A_H = U · diag(μ_i 1[λ ≤ |μ_i|]) · U⊺`. This is
the sum, over the distinct eigenvalues `μ` with `|μ| ≥ λ`, of `μ` times the orthogonal projector
onto its eigenspace, so it does not depend on the choice of eigenbasis. -/
noncomputable def highPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (thr : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
    Matrix.diagonal (fun i => if thr ≤ |hA.eigenvalues i| then hA.eigenvalues i else 0) *
    star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)

/-- **The small-eigenvalue part** `A_L = A − A_H` (Definition 2.3, pp.9–10): the eigenpairs with
eigenvalue of magnitude smaller than `λ`. -/
noncomputable def lowPart {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (thr : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A - highPart A hA thr

/-- **The off-diagonal part** of a square matrix: the diagonal set to zero (p.16: "We split
A′_L = D_L + H_L where D_L is a diagonal matrix and H_L is the off-diagonal matrix of A′_L"). -/
def offDiag {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then 0 else B i j

theorem highPart_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (thr : ℝ) : (highPart A hA thr).IsHermitian := by
  unfold highPart
  rw [Matrix.star_eq_conjTranspose]
  apply Matrix.isHermitian_mul_mul_conjTranspose
  exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by
    ext i; simp)

theorem lowPart_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (thr : ℝ) : (lowPart A hA thr).IsHermitian :=
  hA.sub (highPart_isHermitian hA thr)

end L22EigEst


