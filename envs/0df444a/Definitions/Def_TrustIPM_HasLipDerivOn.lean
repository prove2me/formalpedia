-- Prove2me | Definitions.Def_TrustIPM_HasLipDerivOn
-- name    : TrustIPM_HasLipDerivOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:07.556456+00:00
-- url     : https://prove2.me/theorems/9c9a09e8-e656-4146-b1be-7fabfb9b6230
-- title:
--   Definition 1 — Lipschitz $p$th derivatives (univariate and directional)
-- statement:
--   Let $L_p\in(0,\infty)$ and let $p$ be a nonnegative integer. A univariate function $g:\mathbb R\to\mathbb R$ has **$L_p$-Lipschitz $p$th derivatives on** $S\subseteq\mathbb R$ if for every interval $[\theta_1,\theta_2]\subseteq S$
--
--   $$
--   \bigl|g^{(p)}(\theta_1)-g^{(p)}(\theta_2)\bigr|\le L_p\,|\theta_1-\theta_2| .
--   $$
--
--   A multivariate function $w:\mathbb R^n\to\mathbb R$ has $L_p$-Lipschitz $p$th derivatives on $S\subseteq\mathbb R^n$ if for every $x\in S$ and every $v$ in the closed Euclidean unit ball $B_1(0)$, the univariate function $\theta\mapsto w(x+v\theta)$ has $L_p$-Lipschitz $p$th derivatives on $\{\theta\in\mathbb R: x+v\theta\in S\}$.
--
--   This directional notion is how Assumption 1 bounds the first and second derivatives of the objective and of the constraints on the strictly feasible set; it is weaker than a Lipschitz condition on the derivative map in operator norm.
--
--   **Formalization Note** $g^{(p)}$ is `iteratedDeriv p g`, $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The positivity $L_p>0$ is not built into the predicate; every statement that uses it assumes $L_p>0$ where the paper does.
-- source:
--   Hinder & Ye, Worst-case iteration bounds for log barrier methods on problems with nonconvex constraints, arXiv:1807.00404v5, Definition 1, p.3

import Mathlib

namespace TrustIPM

/-- **Definition 1 (Lipschitz derivatives), univariate part** (Hinder & Ye, *Worst-case iteration
bounds for log barrier methods on problems with nonconvex constraints*, arXiv:1807.00404v5,
Definition 1, p.3). A function `g : ℝ → ℝ` has `L`-Lipschitz `p`th derivatives on `S ⊆ ℝ` if for
every interval `[θ₁, θ₂] ⊆ S` one has `|g⁽ᵖ⁾(θ₁) − g⁽ᵖ⁾(θ₂)| ≤ L |θ₁ − θ₂|`.

**Formalization Note** `g⁽ᵖ⁾` is `iteratedDeriv p g`. The interval `[θ₁, θ₂]` is `Set.Icc θ₁ θ₂`
with `θ₁ ≤ θ₂`. The paper's frame `L ∈ (0, ∞)` is not part of this predicate: every statement that
uses it carries `0 < L` as a hypothesis, where the paper has it. -/
def HasLipDerivOn (p : ℕ) (L : ℝ) (g : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ θ₁ θ₂ : ℝ, θ₁ ≤ θ₂ → Set.Icc θ₁ θ₂ ⊆ S →
    |iteratedDeriv p g θ₁ - iteratedDeriv p g θ₂| ≤ L * |θ₁ - θ₂|

/-- **Definition 1 (Lipschitz derivatives), multivariate part** (Hinder & Ye, arXiv:1807.00404v5,
Definition 1, p.3). A function `w : ℝⁿ → ℝ` has `L`-Lipschitz `p`th derivatives on `S ⊆ ℝⁿ` if for
every `x ∈ S` and every `v ∈ B₁(0)` the univariate function `θ ↦ w(x + vθ)` has `L`-Lipschitz `p`th
derivatives on `{θ ∈ ℝ : x + vθ ∈ S}`.

**Formalization Note** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` and `B₁(0)` is the closed Euclidean unit
ball `‖v‖ ≤ 1`. The condition is directional, exactly as on the page; it is not a Lipschitz
condition on the derivative map in operator norm. -/
def HasLipDerivOnDir {n : ℕ} (p : ℕ) (L : ℝ) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ S, ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 1 →
    HasLipDerivOn p L (fun θ : ℝ => w (x + θ • v)) {θ : ℝ | x + θ • v ∈ S}

end TrustIPM


