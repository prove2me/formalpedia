-- Prove2me | Definitions.Def_ConvexOptAlg_SmoothGD_Defs
-- name    : ConvexOptAlg_SmoothGD_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:44:46.936987+00:00
-- url     : https://prove2.me/theorems/14e2b07c-080b-466f-aa04-20dcdd9d78ff
-- title:
--   §3.2, p. 266 and Eq. (3.1), p. 262 — β-smoothness (gradient β-Lipschitz) and gradient descent runs
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean inner product $x^\top y$ and norm $\|\cdot\|$.
--
--   **β-smoothness.** Let $f:\mathbb R^n\to\mathbb R$ be differentiable with gradient $\nabla f$, and let $\beta\ge0$. The function $f$ is *$\beta$-smooth* if its gradient is $\beta$-Lipschitz:
--
--   $$\|\nabla f(x)-\nabla f(y)\|\le \beta\,\|x-y\|\qquad\text{for all }x,y\in\mathbb R^n.$$
--
--   **Gradient descent.** Given a step size $\eta>0$ and an initial point $x_1\in\mathbb R^n$, gradient descent produces the sequence
--
--   $$x_{t+1}=x_t-\eta\,\nabla f(x_t),\qquad t\ge 1.$$
--
--   These are the two objects of the unconstrained part of §3.2: the smoothness assumption under which gradient descent with $\eta=1/\beta$ attains the rate $O(1/t)$, and the method itself.
--
--   **Formalization Note** The gradient is carried as an explicit map $g:\mathbb R^n\to\mathbb R^n$ together with the hypothesis that $g(x)$ is the gradient of $f$ at every $x$ (`HasGradientAt`). The book asks for a continuously differentiable $f$; continuity of the gradient follows from the Lipschitz bound, so it is not stated separately. Smoothness is the Lipschitz condition on the gradient, not the quadratic upper bound (3.4), which is a consequence (Lemma 3.4). A run is a sequence $x:\mathbb N\to\mathbb R^n$ indexed from $1$ as in the book (index $0$ is unused) together with $\eta>0$; $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, arXiv:1405.4980v2, §3.2, p. 266 (β-smooth) and Eq. (3.1), p. 262

import Mathlib

namespace ConvexOptAlg.SmoothGD

/-- β-smoothness (Bubeck, arXiv:1405.4980v2, §3.2, p. 266): `f : ℝⁿ → ℝ` is differentiable with
gradient map `g` (`∇f(x) = g x` for every `x`), with `β ≥ 0` and gradient β-Lipschitz,
`‖∇f(x) − ∇f(y)‖ ≤ β‖x − y‖` for all `x, y`. Continuity of the gradient (the book's
"continuously differentiable") follows from the Lipschitz bound. This is the book's definition;
the quadratic upper bound (3.4) is a consequence (Lemma 3.4), not the definition. -/
def IsBetaSmooth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) : Prop :=
  0 ≤ β ∧ (∀ x, HasGradientAt f (g x) x) ∧ ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖

/-- A run of gradient descent (Bubeck, arXiv:1405.4980v2, Eq. (3.1), p. 262) with gradient map
`g` and fixed step size `η > 0`: `x (t + 1) = x t − η • g (x t)` for every `t ≥ 1`. The book's
first iterate `x₁` is `x 1`; index `0` is unused and carries no hypothesis. -/
def IsGDRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (η : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  0 < η ∧ ∀ t : ℕ, 1 ≤ t → x (t + 1) = x t - η • g (x t)

end ConvexOptAlg.SmoothGD


