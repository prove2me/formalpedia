-- Prove2me | Definitions.Def_ConvexOptAlg_Subgradient_Defs
-- name    : ConvexOptAlg_Subgradient_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:19:10.813316+00:00
-- url     : https://prove2.me/theorems/9e1a85d1-0192-4a62-bf4d-43e32bdf52cf
-- title:
--   Def. 1.2, Eqs. (3.2)–(3.3), (3.13) — subgradients relative to X, projected subgradient descent runs, strong convexity
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean inner product $x^\top y$ and norm $\|\cdot\|$, $\mathcal X\subseteq\mathbb R^n$ is a set and $f:\mathbb R^n\to\mathbb R$ is a function of which only the values on $\mathcal X$ matter.
--
--   1. **Subgradient relative to $\mathcal X$.** A vector $g\in\mathbb R^n$ is a subgradient of $f$ at $x$ (relative to $\mathcal X$) if
--   $$f(x)-f(y)\le g^\top(x-y)\qquad\text{for every } y\in\mathcal X.$$
--   2. **Projected subgradient descent.** Given step sizes $(\eta_s)_{s\ge1}$ and a horizon $T$, a pair of sequences $(x_s)_{s\ge1}$, $(g_s)_{s\ge1}$ is a run of projected subgradient descent for the steps $s=1,\dots,T$ if $x_1\in\mathcal X$ and, for every $1\le s\le T$, $g_s$ is a subgradient of $f$ at $x_s$ relative to $\mathcal X$ and
--   $$y_{s+1}=x_s-\eta_s g_s,\qquad x_{s+1}=\Pi_{\mathcal X}(y_{s+1}),$$
--   where $x_{s+1}=\Pi_{\mathcal X}(y_{s+1})$ means that $x_{s+1}\in\mathcal X$ is a point of $\mathcal X$ nearest to $y_{s+1}$. Any choice of subgradient is allowed at each step.
--   3. **Strong convexity with subgradients.** For $\alpha\in\mathbb R$, $f$ is $\alpha$-strongly convex on $\mathcal X$ if for all $x,y\in\mathcal X$ and every subgradient $g$ of $f$ at $x$ relative to $\mathcal X$,
--   $$f(x)-f(y)\le g^\top(x-y)-\frac{\alpha}{2}\|x-y\|^2 .$$
--
--   These objects carry the projected subgradient method of Section 3.1 and its strongly convex variant of Section 3.4.1; every rate statement of the mission quantifies over all runs.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. Sequences are indexed by `ℕ` with the first iterate at index $1$ (index $0$ is unused, as in the book). The projection is the published relation `OnlineConvexOpt.FirstOrder.IsMetricProjection`. The run is a predicate on the first $T$ steps rather than an infinite sequence, so that a run of length $T$ needs subgradients only at $x_1,\dots,x_T$.
-- source:
--   Bubeck, arXiv:1405.4980v2, Definition 1.2, p. 235; Eqs. (3.2)–(3.3), p. 264; §3.4.1, p. 277; Eq. (3.13), p. 276

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

namespace ConvexOptAlg.Subgradient

/-- Bubeck, Definition 1.2, p. 235: `g` is a subgradient of `f` at `x` relative to the set `X`
if `f x - f y ≤ gᵀ(x - y)` for every `y ∈ X`. Only the values of `f` on `X` matter. -/
def IsSubgradientOn {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x g : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ X, f x - f y ≤ inner ℝ g (x - y)

/-- Bubeck, §3.1, Eqs. (3.2)–(3.3), p. 264, and §3.4.1, p. 277: `(x, g)` is a run of
projected subgradient descent on `f` over `X` with step sizes `η`, for the steps
`s = 1, …, T`. The first iterate is `x 1 ∈ X` (index `0` is unused); at every step
`1 ≤ s ≤ T`, `g s` is a subgradient of `f` at `x s` relative to `X` (any one of them), and
`x (s + 1)` is the Euclidean projection `Π_X(y_{s+1})` of `y_{s+1} = x s - η s • g s` onto `X`. -/
def IsProjSubgradRun {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (η : ℕ → ℝ)
    (x g : ℕ → EuclideanSpace ℝ (Fin n)) (T : ℕ) : Prop :=
  x 1 ∈ X ∧ ∀ s : ℕ, 1 ≤ s → s ≤ T →
    IsSubgradientOn X f (x s) (g s) ∧
      OnlineConvexOpt.FirstOrder.IsMetricProjection X (x s - η s • g s) (x (s + 1))

/-- Bubeck, Eq. (3.13), p. 276, with a subgradient in place of the gradient ("one can replace
`∇f(x)` in the inequality above by `g ∈ ∂f(x)`"): `f` is `α`-strongly convex on `X` if
`f x - f y ≤ gᵀ(x - y) - (α/2)‖x - y‖²` for all `x, y ∈ X` and every subgradient `g` of `f`
at `x` relative to `X`. -/
def IsStronglyConvexSubgrad {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (α : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, ∀ g : EuclideanSpace ℝ (Fin n), IsSubgradientOn X f x g →
    f x - f y ≤ inner ℝ g (x - y) - α / 2 * ‖x - y‖ ^ 2

end ConvexOptAlg.Subgradient


