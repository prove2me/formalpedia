-- Prove2me | Definitions.Def_CaiCandesShen_ProximalLimit_Basic
-- name    : CaiCandesShen_ProximalLimit_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:23:28.159875+00:00
-- url     : https://prove2.me/theorems/968f391c-6194-44c8-b408-f7744f584ab3
-- title:
--   Frobenius inner product, Frobenius norm, nuclear norm and the proximal objective $f_\tau$ for real matrices
-- statement:
--   This file fixes the basic matrix objects of Cai, Candès and Shen's comparison between the proximal problem and nuclear norm minimization. Throughout, $n_1, n_2$ are natural numbers and $\mathbb R^{n_1\times n_2}$ is the space of real $n_1\times n_2$ matrices.
--
--   1. **Inner product and Frobenius norm.** For $X, Y\in\mathbb R^{n_1\times n_2}$,
--   $$\langle X, Y\rangle = \operatorname{trace}(X^* Y) = \sum_{i,j} X_{ij}Y_{ij},\qquad \|X\|_F = \sqrt{\langle X, X\rangle},$$
--   so that $\|X\|_F^2=\langle X,X\rangle$.
--   2. **Nuclear norm.** $\|X\|_*$ is the sum of the singular values of $X$ (the $1$-norm of the vector of singular values).
--   3. **Proximal objective.** For a parameter $\tau$,
--   $$f_\tau(X) = \tau\|X\|_* + \tfrac12\|X\|_F^2 .$$
--
--   These are the quantities in which the proximal problem (3.4), the nuclear norm problem (1.6) and Theorem 3.1 are stated.
--
--   **Formalization Note** Matrices are `Matrix (Fin n₁) (Fin n₂) ℝ` (abbreviated `Mat n₁ n₂`). The nuclear norm is the sum of Mathlib's `LinearMap.singularValues` of the matrix viewed as a linear map $\mathbb R^{n_2}\to\mathbb R^{n_1}$ between Euclidean spaces. The paper works over $\mathbb R$, so the adjoint $X^*$ is the transpose. $f_\tau$ is defined for every real $\tau$; the paper's standing assumption $\tau>0$ is a hypothesis of each theorem that uses it.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1959 §1.4 (notation); p. 1964 §3.1 and p. 1967 §3.4 (f_τ)

import Mathlib

namespace CaiCandesShen.ProximalLimit

open Matrix

/-- Real `n₁ × n₂` matrices, the ambient space `ℝ^{n₁×n₂}` of the paper. -/
abbrev Mat (n₁ n₂ : ℕ) := Matrix (Fin n₁) (Fin n₂) ℝ

/-- The standard inner product `⟨X, Y⟩ = trace(X* Y) = ∑_{i,j} X_ij Y_ij` (§1.4, p. 1959). -/
def frobInner {n₁ n₂ : ℕ} (X Y : Mat n₁ n₂) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

/-- The Frobenius norm `‖X‖_F = √⟨X, X⟩`, so `‖X‖_F² = ⟨X, X⟩` (§1.4, p. 1959). -/
noncomputable def frobNorm {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : ℝ :=
  Real.sqrt (frobInner X X)

/-- The nuclear norm `‖X‖_*`: the sum of the singular values of `X`, where `X` is viewed as the
linear map `ℝ^{n₂} → ℝ^{n₁}` between Euclidean spaces (§1.4, p. 1959). -/
noncomputable def nuclearNorm {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : ℝ :=
  (Matrix.toEuclideanLin X).singularValues.sum (fun _ s => s)

/-- The proximal objective `f_τ(X) = τ ‖X‖_* + ½ ‖X‖_F²` (§3.1, p. 1964; §3.4, p. 1967). -/
noncomputable def fτ {n₁ n₂ : ℕ} (τ : ℝ) (X : Mat n₁ n₂) : ℝ :=
  τ * nuclearNorm X + 1 / 2 * frobNorm X ^ 2

end CaiCandesShen.ProximalLimit


