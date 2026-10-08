-- Prove2me | Definitions.Def_ProjLikeRetr_Stiefel_matSqrt
-- name    : ProjLikeRetr_Stiefel_matSqrt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:11:39.577994+00:00
-- url     : https://prove2.me/theorems/dcbdfd5f-4bc9-401b-9279-c3c9365c7ffe
-- title:
--   §4.5, p. 22 — the square root √A = U Diag(√λ₁, …, √λ_n) Uᵀ of a symmetric matrix
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be symmetric, with an eigenvalue decomposition $A=U\operatorname{Diag}(\lambda_1,\dots,\lambda_n)U^\top$, $U$ orthogonal. Its **square root** is
--
--   $$\sqrt A=U\operatorname{Diag}\big(\sqrt{\lambda_1},\dots,\sqrt{\lambda_n}\big)U^\top.$$
--
--   When $A$ is positive semidefinite, $\sqrt A$ is the unique symmetric positive-semidefinite matrix whose square is $A$. It enters the closed form of the orthographic retraction on the orthogonal group (Proposition 4.12).
--
--   **Formalization Note** The eigenvalue decomposition is Mathlib's spectral theorem for Hermitian (here real symmetric) matrices (`IsHermitian.eigenvectorUnitary`, `IsHermitian.eigenvalues`). Off the page's domain two junk conventions apply: $\sqrt{\lambda}$ is read as $0$ for $\lambda<0$ (`Real.sqrt`), and a non-symmetric $A$ is sent to the zero matrix. The mission applies the definition only to $I-\Omega^\top\Omega$, which is symmetric, and its statements concern the case in which this matrix is positive semidefinite.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 22, §4.5 (definition of √A before Proposition 4.12)

import Mathlib

open scoped Matrix

namespace ProjLikeRetr.Stiefel

/-- §4.5, p. 22: the square root `√A = U Diag(√λ₁, …, √λₙ) Uᵀ` of a real symmetric matrix `A`, built
from an eigenvalue decomposition `A = U Diag(λ₁, …, λₙ) Uᵀ` (Mathlib's spectral theorem:
`U` = `hA.eigenvectorUnitary`, `λ` = `hA.eigenvalues`). For `A` positive semidefinite this is the
unique positive-semidefinite square root. Two junk conventions, never used by the mission's
statements on their intended inputs: `Real.sqrt` of a negative eigenvalue is `0`, and a
non-symmetric `A` is sent to `0`. -/
noncomputable def matSqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if hA : A.IsHermitian then
    (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal (fun i => Real.sqrt (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ
  else 0

end ProjLikeRetr.Stiefel


