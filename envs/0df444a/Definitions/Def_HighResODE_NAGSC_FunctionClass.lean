-- Prove2me | Definitions.Def_HighResODE_NAGSC_FunctionClass
-- name    : HighResODE_NAGSC_FunctionClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:47.554041+00:00
-- url     : https://prove2.me/theorems/a89a9cdf-e5a1-4113-9e42-cdfd948ed986
-- title:
--   §1.4, p. 8 — the function classes F¹_L(ℝⁿ) and S¹_{μ,L}(ℝⁿ)
-- statement:
--   Let $L>0$. A function $f:\mathbb R^n\to\mathbb R$ belongs to $\mathcal F^1_L(\mathbb R^n)$, the class of **$L$-smooth convex functions**, if it is differentiable,
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle\quad\text{for all }x,y\in\mathbb R^n,$$
--   and its gradient is $L$-Lipschitz: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for all $x,y$, where $\|\cdot\|$ is the Euclidean norm.
--
--   For $0<\mu\le L$, $f$ belongs to $\mathcal S^1_{\mu,L}(\mathbb R^n)$, the class of **$\mu$-strongly convex** members of $\mathcal F^1_L$, if $f\in\mathcal F^1_L(\mathbb R^n)$ and
--   $$f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\frac{\mu}{2}\|y-x\|^2\quad\text{for all }x,y\in\mathbb R^n.$$
--
--   These are the standing function classes of the paper (§1.4): the results on NAG-SC and on the heavy-ball method assume $f\in\mathcal S^1_{\mu,L}$ (or its $C^2$ subclass), and the results on NAG-C assume $f\in\mathcal F^1_L$ (or its $C^2$ subclass).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (abbreviated `E n`) and $\nabla f$ is Mathlib's `gradient f`. Both classes are stated in the page's first-order inequality form; differentiability is an explicit field because the inequalities only make sense for differentiable $f$. The conditions $L>0$ and $0<\mu\le L$ are fields of the structures.
-- source:
--   Shi, Du, Jordan & Su, Understanding the Acceleration Phenomenon via High-Resolution Differential Equations, arXiv:1810.08907v3, p. 8, §1.4 (function classes)

import Mathlib

namespace HighResODE.NAGSC

open scoped InnerProductSpace

/-- The Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- §1.4, p. 8: `f ∈ F¹_L(ℝⁿ)`, the class of `L`-smooth convex functions: `L > 0`,
`f(y) ≥ f(x) + ⟨∇f(x), y − x⟩` for all `x, y`, and `‖∇f(x) − ∇f(y)‖ ≤ L‖x − y‖`. -/
structure IsF1 {n : ℕ} (f : E n → ℝ) (L : ℝ) : Prop where
  L_pos : 0 < L
  differentiable : Differentiable ℝ f
  convex : ∀ x y : E n, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y
  lipschitz_gradient : ∀ x y : E n, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- §1.4, p. 8: `f ∈ S¹_{μ,L}(ℝⁿ)`: `f ∈ F¹_L(ℝⁿ)`, `0 < μ ≤ L`, and
`f(y) ≥ f(x) + ⟨∇f(x), y − x⟩ + (μ/2)‖y − x‖²` for all `x, y`. -/
structure IsS1 {n : ℕ} (f : E n → ℝ) (μ L : ℝ) : Prop where
  isF1 : IsF1 f L
  mu_pos : 0 < μ
  mu_le_L : μ ≤ L
  strongly_convex : ∀ x y : E n, f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y

end HighResODE.NAGSC


