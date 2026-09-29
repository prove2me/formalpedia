-- Prove2me | Definitions.Def_FirstOrderOpt_ConvexTheory_lagrangian
-- name    : FirstOrderOpt_ConvexTheory_lagrangian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T17:35:21.585518+00:00
-- url     : https://prove2.me/theorems/ef82a55e-7af5-41ab-8b4f-a0736d365b8d
-- title:
--   Lagrangian function of the convex program (2.3.16)
-- statement:
--   For the convex program
--   $$f^* \equiv \min_{x \in X} f(x) \quad \text{s.t.} \quad g_i(x) \le 0\ (i=1,\dots,m),\quad
--   h_j(x) = 0\ (j=1,\dots,p), \tag{2.3.16}$$
--   the **Lagrangian function** is
--   $$L(x, \lambda, y) := f(x) + \sum_{i=1}^m \lambda_i g_i(x) + \sum_{j=1}^p y_j h_j(x),$$
--   for multipliers $\lambda_i \ge 0$ ($i=1,\dots,m$) and $y_j \in \mathbb{R}$ ($j=1,\dots,p$),
--   called dual variables or Lagrange multipliers. $L$ relaxes the objective of (2.3.16) by
--   allowing constraint violation at a price set by $\lambda, y$: for any feasible $x$,
--   $L(x,\lambda,y) \le f(x)$ whenever $\lambda \ge 0$.
--
--   **Formalization Note.** $X, f, g, h$ are left as free parameters (not bundled into a
--   structure for problem (2.3.16)), since every mission item that uses $L$ states its own
--   hypotheses on them; `lagrangian` itself only packages the arithmetic expression, matching
--   how the book introduces $L$ before fixing any regularity assumptions on $f, g, h$.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 38, §2.3.1

import Mathlib

namespace FirstOrderOpt.ConvexTheory

/-- The Lagrangian function `L(x, λ, y) = f(x) + Σᵢ λᵢ gᵢ(x) + Σⱼ yⱼ hⱼ(x)` of the convex
program (2.3.16), for `m` inequality constraints `g` and `p` equality constraints `h`. -/
noncomputable def lagrangian {n m p : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (lam : Fin m → ℝ) (y : Fin p → ℝ) : ℝ :=
  f x + ∑ i, lam i * g i x + ∑ j, y j * h j x

end FirstOrderOpt.ConvexTheory


