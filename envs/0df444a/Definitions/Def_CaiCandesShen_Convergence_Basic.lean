-- Prove2me | Definitions.Def_CaiCandesShen_Convergence_Basic
-- name    : CaiCandesShen_Convergence_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:11:18.921314+00:00
-- url     : https://prove2.me/theorems/861e08df-4c9a-42cf-827b-212c1938e64c
-- title:
--   Frobenius inner product, Frobenius and nuclear norms, $f_\tau$, $P_\Omega$ and subgradients for real matrices
-- statement:
--   This file fixes the basic objects of Cai, Candès and Shen's analysis of singular value thresholding. Throughout, $n_1, n_2$ are natural numbers and $\mathbb R^{n_1\times n_2}$ is the space of real $n_1\times n_2$ matrices.
--
--   1. **Inner product and Frobenius norm.** For $X, Y\in\mathbb R^{n_1\times n_2}$,
--   $$\langle X, Y\rangle = \operatorname{trace}(X^* Y) = \sum_{i,j} X_{ij}Y_{ij},\qquad \|X\|_F = \sqrt{\langle X, X\rangle}.$$
--   2. **Nuclear norm.** $\|X\|_*$ is the sum of the singular values of $X$ (the $1$-norm of the vector of singular values).
--   3. **Objective.** For a parameter $\tau$,
--   $$f_\tau(X) = \tau\|X\|_* + \tfrac12\|X\|_F^2 .$$
--   4. **Sampling projector.** For an index set $\Omega\subseteq\{1,\dots,n_1\}\times\{1,\dots,n_2\}$, $P_\Omega(X)$ is the matrix whose $(i,j)$ entry is $X_{ij}$ if $(i,j)\in\Omega$ and $0$ otherwise; it is the orthogonal projector onto the matrices vanishing outside $\Omega$.
--   5. **Subgradient.** $Z$ is a subgradient of $f:\mathbb R^{n_1\times n_2}\to\mathbb R$ at $X_0$, written $Z\in\partial f(X_0)$, if
--   $$f(X)\ge f(X_0)+\langle Z, X-X_0\rangle\quad\text{for all } X.$$
--
--   These are the objects in terms of which the singular value thresholding (SVT) iteration, the proximal problem it solves, and the strong-convexity inequality of Lemma 4.1 are stated.
--
--   **Formalization Note** Matrices are `Matrix (Fin n₁) (Fin n₂) ℝ` (the abbreviation `Mat n₁ n₂`). The nuclear norm is the sum of Mathlib's `LinearMap.singularValues` of the matrix viewed as a linear map $\mathbb R^{n_2}\to\mathbb R^{n_1}$ between Euclidean spaces. $\Omega$ is a `Finset` of index pairs. The paper works over $\mathbb R$, so the adjoint $X^*$ is the transpose.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1958 §1.2 (P_Ω); p. 1959 §1.4 (notation); p. 1960 Eq. (2.4) (subgradient); p. 1963 §2.4 and p. 1964 §3.1 (f_τ)

import Mathlib

namespace CaiCandesShen.Convergence

open Matrix

/-- Real `n₁ × n₂` matrices, the ambient space `ℝ^{n₁×n₂}` of the paper. -/
abbrev Mat (n₁ n₂ : ℕ) := Matrix (Fin n₁) (Fin n₂) ℝ

/-- The standard inner product `⟨X, Y⟩ = trace(X* Y) = ∑_{i,j} X_ij Y_ij` (§1.4, p. 1959). -/
def frobInner {n₁ n₂ : ℕ} (X Y : Mat n₁ n₂) : ℝ :=
  ∑ i, ∑ j, X i j * Y i j

/-- The Frobenius norm `‖X‖_F = √⟨X, X⟩` (§1.4, p. 1959). -/
noncomputable def frobNorm {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : ℝ :=
  Real.sqrt (frobInner X X)

/-- The nuclear norm `‖X‖_*`: the sum of the singular values of `X`, where `X` is viewed as the
linear map `ℝ^{n₂} → ℝ^{n₁}` between Euclidean spaces (§1.4, p. 1959). -/
noncomputable def nuclearNorm {n₁ n₂ : ℕ} (X : Mat n₁ n₂) : ℝ :=
  (Matrix.toEuclideanLin X).singularValues.sum (fun _ s => s)

/-- The objective `f_τ(X) = τ ‖X‖_* + ½ ‖X‖_F²` (§2.4, p. 1963; §3.1, p. 1964). -/
noncomputable def fτ {n₁ n₂ : ℕ} (τ : ℝ) (X : Mat n₁ n₂) : ℝ :=
  τ * nuclearNorm X + 1 / 2 * frobNorm X ^ 2

/-- The sampling projector `P_Ω`: the `(i, j)` entry of `P_Ω(X)` is `X_ij` if `(i, j) ∈ Ω` and
zero otherwise (§1.2, p. 1958). -/
def projΩ {n₁ n₂ : ℕ} (Ω : Finset (Fin n₁ × Fin n₂)) (X : Mat n₁ n₂) : Mat n₁ n₂ :=
  fun i j => if (i, j) ∈ Ω then X i j else 0

/-- `Z` is a subgradient of `f` at `X₀`, `Z ∈ ∂f(X₀)`, if `f(X) ≥ f(X₀) + ⟨Z, X - X₀⟩` for all `X`
(eq. (2.4), p. 1960). -/
def IsSubgradient {n₁ n₂ : ℕ} (f : Mat n₁ n₂ → ℝ) (X₀ Z : Mat n₁ n₂) : Prop :=
  ∀ X, f X₀ + frobInner Z (X - X₀) ≤ f X

end CaiCandesShen.Convergence


