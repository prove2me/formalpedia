-- Prove2me | Definitions.Def_CaiCandesShen_GeneralConvex_Problem
-- name    : CaiCandesShen_GeneralConvex_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:19:06.736898+00:00
-- url     : https://prove2.me/theorems/6f1e68ce-b058-4e3d-a9c8-c88790ea134a
-- title:
--   The constrained problem (3.4), its Lagrangian, primal-dual optimal pairs, and the iteration (3.5)
-- statement:
--   Fix $\tau$ and functions $f_1,\dots,f_m:\mathbb R^{n_1\times n_2}\to\mathbb R$, and write $\mathcal F(X) = (f_1(X),\dots,f_m(X))\in\mathbb R^m$.
--
--   1. **Problem (3.4).** $X^\star$ solves
--   $$\text{minimize } f_\tau(X)\quad\text{subject to } f_i(X)\le 0,\ i=1,\dots,m,$$
--   if $f_i(X^\star)\le 0$ for all $i$ and $f_\tau(X^\star)\le f_\tau(X)$ for every feasible $X$.
--   2. **Lagrangian.** For $X\in\mathbb R^{n_1\times n_2}$ and $y\in\mathbb R^m$,
--   $$\mathcal L(X, y) = f_\tau(X) + \langle y, \mathcal F(X)\rangle .$$
--   3. **Primal-dual optimal pair.** $(X^\star, y^\star)$ is a primal-dual optimal pair if it is a saddle point of $\mathcal L$ over $\mathbb R^{n_1\times n_2}\times\mathbb R^m_+$: $y^\star\ge 0$ and
--   $$\mathcal L(X^\star, y)\le\mathcal L(X^\star, y^\star)\le\mathcal L(X, y^\star)\qquad\text{for all } y\ge 0 \text{ and all } X .$$
--   4. **Iteration (3.5).** Given step sizes $\delta_1,\delta_2,\dots$, sequences $(X^k)$ and $(y^k)$ run the iteration if $y^0 = 0$ and, for $k = 1, 2, \dots$,
--   $$X^k \in \arg\min_X \{ f_\tau(X) + \langle y^{k-1}, \mathcal F(X)\rangle\},\qquad y^k = [\,y^{k-1} + \delta_k\mathcal F(X^k)\,]_+ ,$$
--   where $x_+$ is the vector with entries $\max(x_i, 0)$.
--
--   Iteration (3.5) is Uzawa's method for (3.4) with a projected subgradient step on the dual variable; the saddle-point notion is the paper's meaning of "strong duality holds and $(X^\star,y^\star)$ is primal-dual optimal".
--
--   **Formalization Note** The iteration is a predicate on sequences `X : ℕ → Mat n₁ n₂`, `y : ℕ → Fin m → ℝ`: the paper's step $k$ produces `X (k+1)` and `y (k+1)` from `y k` with step size `δ (k+1)`; `X 0` and `δ 0` are unused. $X^k$ is required to be a minimizer of $\mathcal L(\cdot, y^{k-1})$ rather than computed by a formula; for $\tau>0$ and convex $f_i$ this minimizer exists and is unique. The start $y^0=0$ is the paper's starting point for Uzawa's method ((3.3), p. 1964), which (3.5) follows "just as before".
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1965 §3.2 Eqs. (3.4), (3.5); p. 1963 Eq. (2.11) (saddle point); p. 1964 Eq. (3.3) (y⁰ = 0)

import Mathlib
import Definitions.Def_CaiCandesShen_GeneralConvex_Basic

namespace CaiCandesShen.GeneralConvex

/-- The constraint map `𝓕(X) = (f_1(X), …, f_m(X))` (§3.2, p. 1965). -/
def constraintMap {n₁ n₂ m : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂) : Fin m → ℝ :=
  fun i => f i X

/-- The Lagrangian `𝓛(X, y) = f_τ(X) + ⟨y, 𝓕(X)⟩` of problem (3.4) (§3.2, p. 1965). -/
noncomputable def lagr {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (X : Mat n₁ n₂)
    (y : Fin m → ℝ) : ℝ :=
  fτ τ X + dot y (constraintMap f X)

/-- `Xs` solves problem (3.4), p. 1965: it is feasible, `f_i(Xs) ≤ 0` for all `i`, and
`f_τ(Xs) ≤ f_τ(X)` for every feasible `X`. -/
def IsSol34 {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (Xs : Mat n₁ n₂) : Prop :=
  (∀ i, f i Xs ≤ 0) ∧ ∀ X : Mat n₁ n₂, (∀ i, f i X ≤ 0) → fτ τ Xs ≤ fτ τ X

/-- `(Xs, ys)` is a primal-dual optimal pair of (3.4) in the saddle-point sense of (2.11),
p. 1963: `ys ≥ 0`, `𝓛(Xs, y) ≤ 𝓛(Xs, ys)` for every `y ≥ 0`, and `𝓛(Xs, ys) ≤ 𝓛(X, ys)` for
every `X`. -/
def IsPrimalDualOptimal {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (Xs : Mat n₁ n₂)
    (ys : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ ys i) ∧
    (∀ y : Fin m → ℝ, (∀ i, 0 ≤ y i) → lagr τ f Xs y ≤ lagr τ f Xs ys) ∧
    ∀ X : Mat n₁ n₂, lagr τ f Xs ys ≤ lagr τ f X ys

/-- `(X, y)` is a run of the iteration (3.5), p. 1965, started from `y⁰ = 0` (as in (3.3),
p. 1964): for `k = 1, 2, …`, `X^k` minimizes `𝓛(·, y^{k−1})` and
`y^k = [y^{k−1} + δ_k 𝓕(X^k)]_+`, the positive part taken entrywise. The index `k` of the
paper is the natural number `k`; `X 0` and `δ 0` are not used. -/
def IsGeneralSVTSeq {n₁ n₂ m : ℕ} (τ : ℝ) (f : Fin m → Mat n₁ n₂ → ℝ) (δ : ℕ → ℝ)
    (X : ℕ → Mat n₁ n₂) (y : ℕ → Fin m → ℝ) : Prop :=
  y 0 = 0 ∧
    (∀ k : ℕ, ∀ X' : Mat n₁ n₂, lagr τ f (X (k + 1)) (y k) ≤ lagr τ f X' (y k)) ∧
    ∀ k : ℕ, ∀ i : Fin m,
      y (k + 1) i = max (y k i + δ (k + 1) * constraintMap f (X (k + 1)) i) 0

end CaiCandesShen.GeneralConvex


