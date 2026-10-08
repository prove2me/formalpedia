-- Prove2me | Definitions.Def_ConvexOptAlg_ProjectedGD_Defs
-- name    : ConvexOptAlg_ProjectedGD_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T16:52:43.05308+00:00
-- url     : https://prove2.me/theorems/a93eaba0-be92-4b4c-bdf2-ba13f52faad4
-- title:
--   §3.2, pp. 266–270 — β-smoothness on X, the gradient mapping g_X(x) = β(x − x⁺), and projected gradient descent with η = 1/β
-- statement:
--   This module fixes the objects of the constrained part of §3.2. Throughout, $\mathbb R^n$ carries the Euclidean inner product $x^\top y$ and norm $\|\cdot\|$, and $\mathcal X\subseteq\mathbb R^n$ is the constraint set.
--
--   1. **β-smoothness on $\mathcal X$.** For $\beta\ge0$, a function $f:\mathbb R^n\to\mathbb R$ with gradient map $g$ is *$\beta$-smooth on $\mathcal X$* if $g(x)=\nabla f(x)$ is the gradient of $f$ at every $x\in\mathbb R^n$ and the gradient is $\beta$-Lipschitz on $\mathcal X$:
--   $$\|\nabla f(x)-\nabla f(y)\|\le\beta\|x-y\|\qquad\text{for all }x,y\in\mathcal X .$$
--   2. **Gradient mapping.** For $\beta\in\mathbb R$ and points $x,x^+$, the gradient mapping is $g_{\mathcal X}(x)=\beta(x-x^+)$. It is used with $x^+=\Pi_{\mathcal X}\bigl(x-\tfrac1\beta\nabla f(x)\bigr)$, the projected gradient step from $x$; every statement that uses it assumes this about $x^+$.
--   3. **Projected gradient descent with $\eta=1/\beta$.** For $\beta>0$, a sequence $(x_t)_{t\ge1}$ is a run of projected gradient descent on $\mathcal X$ for the gradient map $g$ if $x_1\in\mathcal X$ and, for every $t\ge1$,
--   $$x_{t+1}=\Pi_{\mathcal X}\Bigl(x_t-\tfrac1\beta\nabla f(x_t)\Bigr),$$
--   where $\Pi_{\mathcal X}(y)$ is a point of $\mathcal X$ nearest to $y$ in the Euclidean norm.
--
--   These are the objects of Lemma 3.6, Theorem 3.7 and Theorem 3.10 of the book; the run is the algorithm whose rate those theorems give.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`. The gradient is an explicit map `g` with `HasGradientAt f (g x) x` at every point, which is how "continuously differentiable" is read: the gradient exists everywhere, so $\nabla f(x)$ makes sense at boundary points of $\mathcal X$ (continuity on $\mathcal X$ follows from the Lipschitz bound). A Lipschitz constant is nonnegative. The projection is the published relation `IsMetricProjection X y p` ($p\in\mathcal X$ and $\|y-p\|\le\|y-z\|$ for all $z\in\mathcal X$); on a nonempty closed convex set it determines $p$ uniquely, so no choice function is used. The run predicate requires $\beta>0$ because its step size is $1/\beta$. The gradient mapping takes the projected point as an argument. The book indexes iterates from $1$; `x 0` is unused.
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, p. 266 (β-smooth), p. 269 (projected gradient descent, the constrained case), Lemma 3.6, p. 270 (g_X); Ch. 3 preamble, pp. 262–263 (Π_X)

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open scoped InnerProductSpace

namespace ConvexOptAlg.ProjectedGD

open OnlineConvexOpt.FirstOrder

/-- `f` is `β`-smooth on `X` with gradient map `g` (Bubeck, arXiv:1405.4980v2, §3.2, p. 266):
`g x` is the gradient `∇f(x)` of `f` at every point `x` of `ℝⁿ`, and the gradient is
`β`-Lipschitz on `X`, with `β ≥ 0`, i.e. `‖∇f(x) − ∇f(y)‖ ≤ β‖x − y‖` for all `x, y ∈ X`. Requiring the gradient
at every point of `ℝⁿ` is the reading of "continuously differentiable"; the Lipschitz bound is
asked on `X` only, as in "β-smooth on X" (Theorem 3.7, p. 270). -/
def IsBetaSmoothOn {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) : Prop :=
  0 ≤ β ∧ (∀ x, HasGradientAt f (g x) x) ∧
    ∀ x ∈ X, ∀ y ∈ X, ‖g x - g y‖ ≤ β * ‖x - y‖

/-- The gradient mapping of Lemma 3.6 (p. 270): `g_X(x) = β (x − x⁺)`, where `x⁺` is the
projected gradient step `Π_X(x − (1/β)∇f(x))` from `x`. The point `x⁺` is passed explicitly;
every statement that uses `gradMap β x xplus` also assumes that `xplus` is that projection. -/
noncomputable def gradMap {n : ℕ} (β : ℝ) (x xplus : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  β • (x - xplus)

/-- `x` is a run of projected gradient descent with step size `η = 1/β` on `X`, for the gradient
map `g` (§3.2, *The constrained case*, p. 269: `x_{t+1} = Π_X(x_t − η∇f(x_t))`): `β > 0`, the first iterate
`x 1` lies in `X`, and for every `t ≥ 1` the iterate `x (t + 1)` is a Euclidean projection onto `X`
of `x t − (1/β) g (x t)`. The book indexes the iterates from `1`; `x 0` is unused and carries no
hypothesis. -/
def IsProjGDRun {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  0 < β ∧ x 1 ∈ X ∧ ∀ t : ℕ, 1 ≤ t →
    IsMetricProjection X (x t - β⁻¹ • g (x t)) (x (t + 1))

end ConvexOptAlg.ProjectedGD


