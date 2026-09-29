-- Prove2me | Definitions.Def_CaiCandesShen_GeneralConvex_Basic
-- name    : CaiCandesShen_GeneralConvex_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:18:31.70285+00:00
-- url     : https://prove2.me/theorems/c74d08fa-ad0b-4300-8f72-7b74165ee4b5
-- title:
--   Frobenius inner product, Frobenius and nuclear norms, $f_\tau$, subgradients, and the Euclidean inner product on $\mathbb R^m$
-- statement:
--   This file fixes the basic objects of Cai, Candès and Shen's analysis of singular value thresholding under general convex constraints. Throughout, $n_1, n_2, m$ are natural numbers and $\mathbb R^{n_1\times n_2}$ is the space of real $n_1\times n_2$ matrices.
--
--   1. **Inner product and Frobenius norm.** For $X, Y\in\mathbb R^{n_1\times n_2}$,
--   $$\langle X, Y\rangle = \operatorname{trace}(X^* Y) = \sum_{i,j} X_{ij}Y_{ij},\qquad \|X\|_F = \sqrt{\langle X, X\rangle}.$$
--   2. **Nuclear norm.** $\|X\|_*$ is the sum of the singular values of $X$.
--   3. **Objective.** For a parameter $\tau$,
--   $$f_\tau(X) = \tau\|X\|_* + \tfrac12\|X\|_F^2 .$$
--   4. **Subgradient.** $Z$ is a subgradient of $g:\mathbb R^{n_1\times n_2}\to\mathbb R$ at $X_0$, written $Z\in\partial g(X_0)$, if
--   $$g(X)\ge g(X_0)+\langle Z, X-X_0\rangle\quad\text{for all } X.$$
--   5. **Euclidean structure on $\mathbb R^m$.** For $u, v\in\mathbb R^m$, $\langle u, v\rangle = \sum_i u_i v_i$ and $\|v\| = \sqrt{\langle v, v\rangle}$.
--
--   These are the objects in which the constrained problem (3.4), its Lagrangian, and the convergence analysis of §4.2 are written.
--
--   **Formalization Note** Matrices are `Matrix (Fin n₁) (Fin n₂) ℝ` (the abbreviation `Mat n₁ n₂`); vectors in $\mathbb R^m$ are functions `Fin m → ℝ`. The nuclear norm is the sum of Mathlib's `LinearMap.singularValues` of the matrix viewed as a linear map $\mathbb R^{n_2}\to\mathbb R^{n_1}$ between Euclidean spaces. The paper works over $\mathbb R$, so the adjoint $X^*$ is the transpose.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1959 §1.4 (notation); p. 1960 Eq. (2.4) (subgradient); p. 1964 §3.1 (f_τ)

import Mathlib

namespace CaiCandesShen.GeneralConvex

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

/-- The objective `f_τ(X) = τ ‖X‖_* + ½ ‖X‖_F²` (§3.1, p. 1964). -/
noncomputable def fτ {n₁ n₂ : ℕ} (τ : ℝ) (X : Mat n₁ n₂) : ℝ :=
  τ * nuclearNorm X + 1 / 2 * frobNorm X ^ 2

/-- `Z` is a subgradient of `g` at `X₀`, `Z ∈ ∂g(X₀)`, if `g(X) ≥ g(X₀) + ⟨Z, X - X₀⟩` for all `X`
(eq. (2.4), p. 1960). -/
def IsSubgradient {n₁ n₂ : ℕ} (g : Mat n₁ n₂ → ℝ) (X₀ Z : Mat n₁ n₂) : Prop :=
  ∀ X, g X₀ + frobInner Z (X - X₀) ≤ g X

/-- The standard inner product `⟨u, v⟩ = ∑_i u_i v_i` on `ℝ^m`. -/
def dot {m : ℕ} (u v : Fin m → ℝ) : ℝ :=
  ∑ i, u i * v i

/-- The Euclidean norm `‖v‖ = √⟨v, v⟩` on `ℝ^m`. -/
noncomputable def eucNorm {m : ℕ} (v : Fin m → ℝ) : ℝ :=
  Real.sqrt (dot v v)

end CaiCandesShen.GeneralConvex


