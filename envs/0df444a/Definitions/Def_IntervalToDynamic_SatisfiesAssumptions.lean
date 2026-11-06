-- Prove2me | Definitions.Def_IntervalToDynamic_SatisfiesAssumptions
-- name    : IntervalToDynamic_SatisfiesAssumptions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:46.853193+00:00
-- url     : https://prove2.me/theorems/339f7857-df4b-4960-8be4-8ca0248e6dbf
-- title:
--   Assumptions 1 and 2 for one loss and the selected class
-- statement:
--   A loss $f$ with gradient $\nabla f$ satisfies the standing assumptions of the selected class when:
--
--   1. (Assumption 1) $\mathcal X$ is convex, compact and nonempty, $\mathcal X\subseteq\mathcal B(D_{\mathcal X}/2)$ with $D_{\mathcal X}>0$; for a fixed $G>0$, $f$ is differentiable and convex on $\mathcal X$ and $\|\nabla f(x)\|_2\le G$ for every $x\in\mathcal X$.
--   2. (Assumption 2, exp-concave regime) $\alpha>0$ and $x\mapsto\exp(-\alpha f(x))$ is concave on $\mathcal X$.
--   3. (Assumption 2, strongly convex regime) $\lambda>0$ and $f(u)\ge f(x)+\nabla f(x)^\top(u-x)+\frac\lambda2\|u-x\|_2^2$ for every $x,u\in\mathcal X$.
--
--   Assumption 1 applies in all three regimes.
--
--   **Formalization Note** "Differentiable on $\mathcal X$" is a gradient oracle `gr` with `HasGradientWithinAt f (gr x) X x`, because $\mathcal X$ may have empty interior, so that neither ambient differentiability nor Mathlib's `gradient` is available. Nonemptiness is implicit in the paper: $\Pi_{\mathcal X}$ and $\mathcal X^T$ presuppose it.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Assumption 1, p.7; Assumption 2, p.8

import Mathlib
import Definitions.Def_IntervalToDynamic_LossMode
import Definitions.Def_LogRegretOCO_ONS_IsExpConcaveOn

namespace IntervalToDynamic

/-- Assumption 1 and, for the selected loss class, Assumption 2, for one loss `f` with gradient
oracle `gr`. Wang–Zhao–Zhou, *On the Relation Between Interval Regret and Dynamic Regret*, arXiv:2609.34423, Assumption 1, p.7, and Assumption 2, p.8.

Assumption 1: `X` is convex and compact, `X ⊆ B(D_X/2)` for a fixed `D_X > 0`; for a fixed `G > 0`,
the loss is differentiable and convex on `X` with `‖∇f(x)‖₂ ≤ G` for every `x ∈ X`.
Assumption 2: in the exp-concave regime `x ↦ exp(−α f(x))` is concave on `X` for a fixed `α > 0`;
in the strongly convex regime `f(u) ≥ f(x) + ∇f(x)ᵀ(u − x) + (λ/2)‖u − x‖₂²` on `X²` for a fixed
`λ > 0`.

**Formalization Note.** "Differentiable on `X`" is `HasGradientWithinAt f (gr x) X x` for a gradient
oracle `gr`, because `X` may have empty interior: neither ambient differentiability nor Mathlib's
`gradient f` is available there. Assumption 1 applies in all three regimes. `X` is nonempty because
`Π_X` and `X^T` presuppose it. The strong convexity inequality is the printed one, with `gr` in
place of `∇f`. -/
structure SatisfiesAssumptions {d : ℕ} (mode : LossMode) (X : Set (EuclideanSpace ℝ (Fin d))) (DX G : ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (gr : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop where
  isCompact : IsCompact X
  convex : Convex ℝ X
  nonempty : X.Nonempty
  subset_ball : X ⊆ Metric.closedBall 0 (DX / 2)
  DX_pos : 0 < DX
  G_pos : 0 < G
  convexOn : ConvexOn ℝ X f
  hasGradient : ∀ x ∈ X, HasGradientWithinAt f (gr x) X x
  grad_bound : ∀ x ∈ X, ‖gr x‖ ≤ G
  curvature :
    match mode with
    | .convex => True
    | .expConcave α => 0 < α ∧ LogRegretOCO.ONS.IsExpConcaveOn α X f
    | .stronglyConvex lam =>
        0 < lam ∧ ∀ x ∈ X, ∀ u ∈ X,
          f x + inner ℝ (gr x) (u - x) + (lam / 2) * ‖u - x‖ ^ 2 ≤ f u

end IntervalToDynamic


