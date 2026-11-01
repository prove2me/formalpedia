-- Prove2me | Definitions.Def_VRAccelCLT_SmoothStronglyConvex
-- name    : VRAccelCLT_SmoothStronglyConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:05.17774+00:00
-- url     : https://prove2.me/theorems/203b9605-ab2b-4809-8827-bcef8198c54d
-- title:
--   Assumption 1 (i)–(ii): $L$-smooth, $\eta$-strongly convex $f$
-- statement:
--   A function $f:\mathbb R^m\to\mathbb R$ satisfies **Assumption 1 (i)–(ii)** with constants $L>0$ and $\eta>0$ if
--
--   1. $f$ is continuously differentiable and its gradient is $L$-Lipschitz: $\|\nabla f(x)-\nabla f(x')\|\le L\|x-x'\|$ for all $x,x'\in\mathbb R^m$;
--   2. $f$ is $\eta$-strongly convex in the gradient form
--   $$
--   (\nabla f(x)-\nabla f(x'))^{T}(x-x')\ \ge\ \eta\|x-x'\|^{2}\qquad\text{for all }x,x'\in\mathbb R^m .
--   $$
--
--   These are the standing smoothness and convexity assumptions on the objective $f(x)=\mathbb E[F(x,\xi)]$ of problem (1). Under them $f$ has a unique minimizer $x^*$ with $\nabla f(x^*)=0$.
--
--   **Formalization Note** $\mathbb R^m$ is the Euclidean space on $m$ coordinates and $\nabla f$ is Mathlib's gradient. Assumption 1 (iii), the condition on the sampled gradients, enters only through its consequence (5); see the noise definition `IsVRNoise`.
-- source:
--   Lei, Shanbhag, Variance-Reduced Accelerated First-order Methods: Central Limit Theorems and Confidence Statements, arXiv:2006.07769v3, Assumption 1 (i)–(ii), pp.6–7

import Mathlib

namespace VRAccelCLT

/-- **Assumption 1 (i)–(ii)**: `f` is continuously differentiable with an `L`-Lipschitz gradient
and is `η`-strongly convex. Lei, Shanbhag, arXiv:2006.07769v3, Assumption 1, pp.6–7:
"(i) f is continuously differentiable on Rm with a Lipschitz continuous gradient, i.e., there exists
a constant L > 0 such that ∥∇f(x) −∇f(x′)∥ ≤ L∥x −x′∥ for any x, x′ ∈ Rm. (ii) f is η-strongly
convex, i.e., (∇f(x) −∇f(x′))T (x −x′) ≥ η∥x −x′∥2 for any x, x′ ∈ Rm."

**Formalization Note.** `ℝᵐ` is `EuclideanSpace ℝ (Fin m)` and `∇f` is Mathlib's `gradient f`.
Strong convexity is stated in the paper's own gradient form (ii). The constant `η` is positive
(the paper uses `0 < η` throughout, e.g. p.17). Assumption 1 (iii), the oracle condition, enters this
formalization only through its consequence (5) on the noise; see `IsVRNoise`. -/
def SmoothStronglyConvex {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) (L η : ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ 0 < L ∧
    (∀ x x' : EuclideanSpace ℝ (Fin m), ‖gradient f x - gradient f x'‖ ≤ L * ‖x - x'‖) ∧
    0 < η ∧
    ∀ x x' : EuclideanSpace ℝ (Fin m),
      η * ‖x - x'‖ ^ 2 ≤ inner ℝ (gradient f x - gradient f x') (x - x')

end VRAccelCLT


