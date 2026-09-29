-- Prove2me | Definitions.Def_LogRegretOCO_OGD_Model
-- name    : LogRegretOCO_OGD_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:32:03.346732+00:00
-- url     : https://prove2.me/theorems/12e29586-3fed-4f83-aad8-ecfef10cde8f
-- title:
--   Euclidean projection, H-strong convexity, and the Online Gradient Descent run (§2.2, Fig. 1)
-- statement:
--   This file fixes the objects of Hazan, Agarwal and Kale's analysis of ONLINE GRADIENT DESCENT. Points live in $\mathbb R^n$ with the Euclidean norm $\|\cdot\|_2$.
--
--   1. **Euclidean projection.** For a set $\mathcal P\subseteq\mathbb R^n$ and $y\in\mathbb R^n$, a point $z$ is *the projection of $y$ onto $\mathcal P$*, written $z=\Pi_{\mathcal P}(y)$, when
--   $$z\in\mathcal P\quad\text{and}\quad \|z-y\|_2\le\|w-y\|_2\ \text{ for every } w\in\mathcal P,$$
--   that is, $z\in\arg\min_{x\in\mathcal P}\|x-y\|_2$. For a nonempty, closed, convex $\mathcal P$ such a point exists and is unique.
--
--   2. **$H$-strong convexity.** A function $f:\mathbb R^n\to\mathbb R$ is *$H$-strongly convex on $\mathcal P$* when it is differentiable, its derivative is differentiable at every point of $\mathcal P$, and its Hessian is bounded below by $H I_n$ there:
--   $$\forall x\in\mathcal P:\quad \nabla^2 f(x)\succeq H I_n,\qquad\text{i.e.}\qquad v^\top\nabla^2 f(x)\,v\ \ge\ H\|v\|_2^2\ \text{ for all } v\in\mathbb R^n.$$
--
--   3. **The Online Gradient Descent run (Fig. 1).** Given a set $\mathcal P$, step sizes $\eta_1,\eta_2,\dots$ and cost functions $f_1,f_2,\dots$, a sequence $x_1,x_2,\dots$ is a run of ONLINE GRADIENT DESCENT when $x_1\in\mathcal P$ is arbitrary and, in every iteration $t>1$,
--   $$x_t=\Pi_{\mathcal P}\bigl(x_{t-1}-\eta_t\nabla f_{t-1}(x_{t-1})\bigr).$$
--
--   These are the algorithm and the curvature assumption under which the paper proves its first logarithmic regret bound (Theorem 1).
--
--   **Formalization Note** Points are `EuclideanSpace ℝ (Fin n)`. The run is a predicate on the whole trajectory, required at every round, with 1-based rounds: `x 0`, `f 0` and `η 1` are never read, and the rule is written as $x_{t+1}=\Pi_{\mathcal P}(x_t-\eta_{t+1}\nabla f_t(x_t))$ for $t\ge1$, which is Fig. 1's rule with the index shifted. The Hessian is the second Fréchet derivative `fderiv ℝ (fderiv ℝ f) x`, and $\nabla f$ is Mathlib's `gradient`. Cost functions are defined on all of $\mathbb R^n$ (the paper writes $f_t:\mathcal P\to\mathbb R$ but differentiates them as functions on $\mathbb R^n$). The number $H$ is unrestricted in the definition; the paper's $H>0$ is a hypothesis of Theorem 1.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 172, §2.2 (Hessian lower bound, H-strong convexity) and p. 174, Fig. 1 (Online Gradient Descent, Euclidean projection)

import Mathlib

namespace LogRegretOCO.OGD

/-- Points of the decision space: `ℝⁿ` with the Euclidean norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `IsProj P y z`: `z` is the Euclidean projection of `y` onto `P`,
`z = Π_P(y) = argmin_{x ∈ P} ‖x − y‖₂` (Fig. 1, p. 174). For a nonempty closed convex `P`
exactly one such `z` exists. -/
def IsProj {n : ℕ} (P : Set (E n)) (y z : E n) : Prop :=
  z ∈ P ∧ ∀ w ∈ P, ‖z - y‖ ≤ ‖w - y‖

/-- `IsHStrongConvex P H f` (§2.2, p. 172): `f` is twice differentiable and its Hessian is
bounded below by `H I_n` at every point of `P`, i.e. `∇²f(x) ⪰ H I_n` for `x ∈ P`, written as
`vᵀ ∇²f(x) v ≥ H ‖v‖²` for every `v`, with `∇²f(x)` the second Fréchet derivative. -/
def IsHStrongConvex {n : ℕ} (P : Set (E n)) (H : ℝ) (f : E n → ℝ) : Prop :=
  Differentiable ℝ f ∧ (∀ x ∈ P, DifferentiableAt ℝ (fderiv ℝ f) x) ∧
    ∀ x ∈ P, ∀ v : E n, H * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v

/-- `IsOGDRun P η f x` (Fig. 1, p. 174): `x` is a run of ONLINE GRADIENT DESCENT on the convex
set `P` with step sizes `η 1, η 2, …` against the cost functions `f 1, f 2, …`. Rounds are
1-based (`x 0`, `f 0` and `η 1` are never used): `x 1 ∈ P` is arbitrary, and in iteration
`t + 1 > 1` the point is `x (t + 1) = Π_P(x t − η (t + 1) ∇f_t(x t))`. -/
def IsOGDRun {n : ℕ} (P : Set (E n)) (η : ℕ → ℝ) (f : ℕ → E n → ℝ) (x : ℕ → E n) : Prop :=
  x 1 ∈ P ∧ ∀ t : ℕ, 1 ≤ t → IsProj P (x t - η (t + 1) • gradient (f t) (x t)) (x (t + 1))

end LogRegretOCO.OGD


