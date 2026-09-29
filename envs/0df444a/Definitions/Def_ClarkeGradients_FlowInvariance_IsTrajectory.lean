-- Prove2me | Definitions.Def_ClarkeGradients_FlowInvariance_IsTrajectory
-- name    : ClarkeGradients_FlowInvariance_IsTrajectory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:38:55.099636+00:00
-- url     : https://prove2.me/theorems/b2c0bd84-df71-4e59-9843-1e3fe1f6d4fc
-- title:
--   (4.1) — trajectory of a multifunction (absolutely continuous solution of ẋ ∈ X(x))
-- statement:
--   Let $X$ be a multifunction from $\mathbb R^n$ to $\mathbb R^n$, that is, $X(x)\subseteq\mathbb R^n$ for each $x\in\mathbb R^n$. A **trajectory** for $X$ is an absolutely continuous function $x:[0,1]\to\mathbb R^n$ such that
--
--   $$
--   \dot x(t)\in X(x(t))\qquad\text{for almost all } t\in[0,1],
--   $$
--
--   where $\dot x(t)$ is the derivative of $x$, which exists almost everywhere. The relation $\dot x\in X(x)$ is a **differential inclusion**, a generalized differential equation.
--
--   Trajectories are the curves quantified over in the definition (4.3) of a flow-invariant set.
--
--   **Formalization Note** The curve is a function $x:\mathbb R\to\mathbb R^n$ that is absolutely continuous on $[0,1]$ (Mathlib's `AbsolutelyContinuousOnInterval x 0 1`). The almost-everywhere clause is taken with respect to Lebesgue measure restricted to $[0,1]$ and reads: $x$ is differentiable at $t$ with some derivative $w\in X(x(t))$. It is written with `HasDerivAt` rather than `deriv x t ∈ X (x t)`, because `deriv` returns $0$ where $x$ is not differentiable. Values of $x$ outside $[0,1]$ play no role: the a.e. clause ignores the two endpoints, and the derivative at an interior point depends only on nearby values. Absolute continuity is essential: without it a Cantor-type curve with $\dot x=0$ a.e. would count as a trajectory of $X\equiv\{0\}$.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 259, §4, (4.1)

import Mathlib

open MeasureTheory

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), §4, (4.1): a *trajectory* for the multifunction `X : ℝⁿ → 2^{ℝⁿ}` is an
absolutely continuous function `x : [0, 1] → ℝⁿ` such that `ẋ(t) ∈ X(x(t))` for almost all
`t ∈ [0, 1]`. Here `x` is a function on `ℝ`, absolutely continuous on `[0, 1]`, and the a.e.
condition says that for almost every `t ∈ [0, 1]`, `x` is differentiable at `t` with derivative
in `X(x(t))`; values of `x` outside `[0, 1]` play no role. -/
def IsTrajectory {n : ℕ} (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  AbsolutelyContinuousOnInterval x 0 1 ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∃ w ∈ X (x t), HasDerivAt x w t

end ClarkeGradients.FlowInvariance


