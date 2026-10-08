-- Prove2me | Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
-- name    : ConvexOptAlg_NesterovSmooth_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:36:06.956043+00:00
-- url     : https://prove2.me/theorems/172f014a-e1c2-4df7-aef8-2b97f02b9475
-- title:
--   §3.2, p. 266 and §3.7.2, pp. 293–294 — β-smoothness, the sequences λ_t, γ_t and Nesterov's accelerated gradient descent (smooth case)
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean inner product $x^\top y$ and norm $\|\cdot\|$.
--
--   **β-smoothness.** Let $f:\mathbb R^n\to\mathbb R$ be differentiable with gradient $\nabla f$, and let $\beta\in\mathbb R$. The function $f$ is *$\beta$-smooth* if its gradient is $\beta$-Lipschitz:
--
--   $$\|\nabla f(x)-\nabla f(y)\|\le \beta\,\|x-y\|\qquad\text{for all }x,y\in\mathbb R^n.$$
--
--   **The step sequences.** Define $\lambda_0=0$ and, for $t\ge1$,
--
--   $$\lambda_t=\frac{1+\sqrt{1+4\lambda_{t-1}^2}}{2},\qquad \gamma_t=\frac{1-\lambda_t}{\lambda_{t+1}}.$$
--
--   Then $\lambda_1=1$ and $\lambda_t\ge1$ for $t\ge1$, so $\gamma_t$ is well defined, and $\gamma_t\le0$.
--
--   **Nesterov's accelerated gradient descent (smooth case).** Starting from an arbitrary point $x_1=y_1\in\mathbb R^n$, the method produces two sequences by
--
--   $$y_{t+1}=x_t-\frac1\beta\nabla f(x_t),\qquad x_{t+1}=(1-\gamma_t)\,y_{t+1}+\gamma_t\,y_t,\qquad t\ge1.$$
--
--   The sequence $(y_t)$ is the primary sequence, obtained by gradient steps of length $1/\beta$; $(x_t)$ is a time-varying combination of its last two elements. These are the objects of §3.7.2, in which the method attains the rate $O(1/t^2)$ on convex $\beta$-smooth functions.
--
--   **Formalization Note** The gradient is carried as an explicit map $g$ with $g(x)=\nabla f(x)$ at every $x$ (`HasGradientAt`); continuity of the gradient (the book's "continuously differentiable") follows from the Lipschitz bound. $\lambda$ is a real sequence defined by recursion on $\mathbb N$ and $\gamma_t$ is a real division, whose denominator $\lambda_{t+1}\ge1$ never vanishes. A run is a pair of sequences $x,y:\mathbb N\to\mathbb R^n$ indexed from $1$ as in the book (index $0$ is unused and constrained by nothing). The page prints the second update as $x_{t+1}=(1-\gamma_s)y_{t+1}+\gamma_t y_t$; the index $s$ is a misprint for $t$, as the proof's display (3.26), $x_{s+1}=y_{s+1}+\gamma_s(y_s-y_{s+1})$, shows. $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, arXiv:1405.4980v2, §3.2, p. 266 (β-smooth) and §3.7.2, pp. 293–294 (λ_t, γ_t, the algorithm)

import Mathlib

namespace ConvexOptAlg.NesterovSmooth

/-- β-smoothness (Bubeck, arXiv:1405.4980v2, §3.2, p. 266): `f : ℝⁿ → ℝ` is differentiable with
gradient map `g` (`∇f(x) = g x` for every `x`), and the gradient is β-Lipschitz,
`‖∇f(x) − ∇f(y)‖ ≤ β‖x − y‖` for all `x, y`. Continuity of the gradient (the book's
"continuously differentiable") follows from the Lipschitz bound. -/
def IsBetaSmooth {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) : Prop :=
  (∀ x, HasGradientAt f (g x) x) ∧ ∀ x y, ‖g x - g y‖ ≤ β * ‖x - y‖

/-- The sequence `λ_t` of §3.7.2 (Bubeck, arXiv:1405.4980v2, p. 293):
`λ₀ = 0`, `λ_t = (1 + √(1 + 4λ_{t−1}²))/2` for `t ≥ 1`. -/
noncomputable def lam : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 + Real.sqrt (1 + 4 * lam t ^ 2)) / 2

/-- The coefficients `γ_t = (1 − λ_t)/λ_{t+1}` of §3.7.2 (p. 293). The denominator is never zero:
`λ_{t+1} ≥ 1` for every `t`. -/
noncomputable def gam (t : ℕ) : ℝ := (1 - lam t) / lam (t + 1)

/-- A run of Nesterov's accelerated gradient descent for the smooth case (Bubeck,
arXiv:1405.4980v2, §3.7.2, p. 294), with gradient map `g` and smoothness constant `β`:
`x₁ = y₁` is an arbitrary initial point and, for every `t ≥ 1`,
`y_{t+1} = x_t − (1/β)∇f(x_t)` and `x_{t+1} = (1 − γ_t) y_{t+1} + γ_t y_t`.
The page prints `(1 − γ_s)` in the second equation; the proof's (3.26),
`x_{s+1} = y_{s+1} + γ_s (y_s − y_{s+1})`, shows the coefficient is `γ_t`.
Indices start at `1` as in the book; index `0` is unused and carries no hypothesis. -/
def IsNesterovRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 1 = y 1 ∧
    ∀ t : ℕ, 1 ≤ t →
      y (t + 1) = x t - (1 / β) • g (x t) ∧
        x (t + 1) = (1 - gam t) • y (t + 1) + gam t • y t

end ConvexOptAlg.NesterovSmooth


