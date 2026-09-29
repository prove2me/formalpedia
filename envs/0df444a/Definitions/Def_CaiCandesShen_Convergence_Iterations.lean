-- Prove2me | Definitions.Def_CaiCandesShen_Convergence_Iterations
-- name    : CaiCandesShen_Convergence_Iterations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:13:11.75395+00:00
-- url     : https://prove2.me/theorems/03ce87f0-367b-4e6c-b30c-91f8d623361a
-- title:
--   The SVT iteration (2.7) from $Y^0=0$ and Uzawa's iteration (3.3) from $y^0=0$
-- statement:
--   Fix $\tau$, a sequence of step sizes $\{\delta_k\}_{k\ge1}$, an index set $\Omega$ and $M\in\mathbb R^{n_1\times n_2}$.
--
--   1. **SVT iteration (2.7).** Starting with $Y^0=0$, define for $k=1,2,\dots$
--   $$X^k=\mathcal D_\tau(Y^{k-1}),\qquad Y^k=Y^{k-1}+\delta_kP_\Omega(M-X^k).$$
--   2. **Uzawa's iteration (3.3).** For a linear map $\mathcal A:\mathbb R^{n_1\times n_2}\to\mathbb R^m$ and $b\in\mathbb R^m$, starting with $y^0=0$, define for $k=1,2,\dots$
--   $$X^k=\mathcal D_\tau(\mathcal A^*(y^{k-1})),\qquad y^k=y^{k-1}+\delta_k(b-\mathcal A(X^k)).$$
--
--   A pair of sequences "runs" an iteration if it satisfies these recursions for every $k\ge1$. The SVT iteration is the matrix-completion algorithm of the paper; Uzawa's iteration is the general form it takes under linear equality constraints.
--
--   **Formalization Note** Sequences are indexed by $\mathbb N$; the paper's step $k$ is the Lean step `k+1`, so `X 0` and `δ 0` are never used. The start $Y^0=0$ is fixed in (1.5), §2.4 and §5.1.3 of the paper, and $y^0=0$ is printed in (3.3).
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1958 Eq. (1.5) (Y⁰ = 0); p. 1961 Eq. (2.7); p. 1964 Eq. (3.3)

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Shrink
import Definitions.Def_CaiCandesShen_Convergence_Problems

namespace CaiCandesShen.Convergence

open Matrix

/-- `(X, Y)` is a run of the SVT iteration (2.7), p. 1961, started from `Y⁰ = 0` (eq. (1.5),
p. 1958): for `k = 1, 2, …`, `X^k = D_τ(Y^{k−1})` and `Y^k = Y^{k−1} + δ_k P_Ω(M - X^k)`.
The index `k` of the paper is the natural number `k`; `X 0` and `δ 0` are not used. -/
def IsSVTSeq {n₁ n₂ : ℕ} (τ : ℝ) (Ω : Finset (Fin n₁ × Fin n₂)) (M : Mat n₁ n₂) (δ : ℕ → ℝ)
    (X Y : ℕ → Mat n₁ n₂) : Prop :=
  Y 0 = 0 ∧ ∀ k : ℕ, IsShrink τ (Y k) (X (k + 1)) ∧
    Y (k + 1) = Y k + δ (k + 1) • projΩ Ω (M - X (k + 1))

/-- `(X, y)` is a run of Uzawa's iteration (3.3), p. 1964, started from `y⁰ = 0`: for
`k = 1, 2, …`, `X^k = D_τ(𝒜*(y^{k−1}))` and `y^k = y^{k−1} + δ_k (b - 𝒜(X^k))`.
`X 0` and `δ 0` are not used. -/
def IsUzawaSeq {n₁ n₂ m : ℕ} (τ : ℝ) (Aop : Fin m → Mat n₁ n₂) (b : Fin m → ℝ) (δ : ℕ → ℝ)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) : Prop :=
  y 0 = 0 ∧ ∀ k : ℕ, IsShrink τ (adjA Aop (y k)) (X (k + 1)) ∧
    y (k + 1) = y k + δ (k + 1) • (b - applyA Aop (X (k + 1)))

end CaiCandesShen.Convergence


