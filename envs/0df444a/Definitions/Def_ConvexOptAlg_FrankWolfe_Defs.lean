-- Prove2me | Definitions.Def_ConvexOptAlg_FrankWolfe_Defs
-- name    : ConvexOptAlg_FrankWolfe_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:02:08.256401+00:00
-- url     : https://prove2.me/theorems/eb6a81a8-0eb0-4a05-a9e2-71765ed3bde4
-- title:
--   §3.3, Eqs. (3.8)–(3.9), pp. 271–272 — β-smoothness in an arbitrary norm and conditional gradient (Frank–Wolfe) runs
-- statement:
--   Throughout, $E$ is a finite-dimensional real vector space with an arbitrary norm $\|\cdot\|$, $\mathcal X\subseteq E$ is a set, and $f:E\to\mathbb R$ is differentiable with gradient $\nabla f(x)$, a linear form on $E$ whose value at $v$ is written $\nabla f(x)^\top v$. The **dual norm** of a linear form $g$ is $\|g\|_*=\sup_{\|v\|\le1}g^\top v$.
--
--   1. **β-smoothness in a norm.** For $\beta\in\mathbb R$, $f$ is $\beta$-smooth with respect to $\|\cdot\|$ on $\mathcal X$ if $f$ is differentiable everywhere and
--   $$\|\nabla f(x)-\nabla f(y)\|_*\le\beta\,\|x-y\|\qquad\text{for all }x,y\in\mathcal X .$$
--   2. **Conditional gradient descent (Frank–Wolfe).** Given a sequence of step sizes $(\gamma_s)_{s\ge1}$, a pair of sequences $(x_t)_{t\ge1}$, $(y_t)_{t\ge1}$ is a run of conditional gradient descent on $\mathcal X$ if $x_1\in\mathcal X$ and, for every $t\ge1$,
--   $$y_t\in\operatorname*{argmin}_{y\in\mathcal X}\nabla f(x_t)^\top y,\qquad x_{t+1}=(1-\gamma_t)\,x_t+\gamma_t\,y_t .$$
--   Any minimizer of the linear form may be chosen as $y_t$.
--
--   These two objects carry Section 3.3: the method replaces the projection of projected gradient descent by a linear minimization over $\mathcal X$, and its analysis adapts to smoothness measured in any norm.
--
--   **Formalization Note** The gradient is given as an explicit derivative map `f' : E → (E →L[ℝ] ℝ)` with `HasFDerivAt f (f' x) x` for every `x`, so $\nabla f(x)^\top v$ is `f' x v`, and the dual norm is the operator norm on `E →L[ℝ] ℝ`, which equals $\sup_{\|v\|\le1}g^\top v$. The Lipschitz condition is required on $\mathcal X$ (the only points the method visits). Sequences are indexed by `ℕ` with the first iterate at index $1$; index $0$ is unused, as in the book. The book's $\mathbb R^n$ with an arbitrary norm is a finite-dimensional real normed space.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.3, Eqs. (3.8)–(3.9), p. 271, and the definition of β-smoothness in a norm, p. 272

import Mathlib

namespace ConvexOptAlg.FrankWolfe

/-- β-smoothness in an arbitrary norm (Bubeck, arXiv:1405.4980v2, §3.3, p. 272): `f : E → ℝ` is
differentiable with derivative map `f'` (`∇f(x)` acting by `∇f(x)⊤y = f' x y`), and the gradient
is β-Lipschitz from `‖·‖` to the dual norm on `X`: `‖∇f(x) − ∇f(y)‖∗ ≤ β‖x − y‖` for `x, y ∈ X`.
The dual norm `‖g‖∗ = sup_{‖x‖≤1} g⊤x` is the operator norm of `g : E →L[ℝ] ℝ`. -/
def IsBetaSmoothNormOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (β : ℝ) : Prop :=
  (∀ x, HasFDerivAt f (f' x) x) ∧ ∀ x ∈ X, ∀ y ∈ X, ‖f' x - f' y‖ ≤ β * ‖x - y‖

/-- A run of conditional gradient descent (Frank–Wolfe), Bubeck, arXiv:1405.4980v2, §3.3,
Eqs. (3.8)–(3.9), p. 271, with derivative map `f'` and step sizes `(γ_s)_{s≥1}`: the first
iterate `x 1` lies in `X` (index `0` is unused), and for every `t ≥ 1`, `y t` is any minimizer
over `X` of the linear form `∇f(x_t)⊤y` (3.8), and `x (t + 1) = (1 − γ_t) x_t + γ_t y_t` (3.9). -/
def IsFrankWolfeRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f' : E → E →L[ℝ] ℝ) (γ : ℕ → ℝ) (x y : ℕ → E) : Prop :=
  x 1 ∈ X ∧ ∀ t : ℕ, 1 ≤ t →
    (y t ∈ X ∧ ∀ z ∈ X, f' (x t) (y t) ≤ f' (x t) z) ∧
      x (t + 1) = (1 - γ t) • x t + γ t • y t

end ConvexOptAlg.FrankWolfe


