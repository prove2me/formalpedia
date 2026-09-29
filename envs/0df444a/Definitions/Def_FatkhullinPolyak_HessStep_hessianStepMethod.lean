-- Prove2me | Definitions.Def_FatkhullinPolyak_HessStep_hessianStepMethod
-- name    : FatkhullinPolyak_HessStep_hessianStepMethod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:48:55.266991+00:00
-- url     : https://prove2.me/theorems/b4a8c677-c6bb-4caa-b1e4-adf97b2acd35
-- title:
--   Gradient descent with the Hessian step size (6.1) and its damped version
-- statement:
--   Let $f:\mathbb{R}^n\to\mathbb{R}$ be a function on Euclidean space, with gradient $\nabla f(x)$ and Hessian $\nabla^2 f(x)$. This file fixes four objects.
--
--   1. The **Hessian quadratic form** $\langle \nabla^2 f(x)v, v\rangle$, i.e. the second derivative of $f$ at $x$ applied twice to the direction $v$.
--   2. The **Hessian step size** at a point $x$,
--   $$
--   \gamma(x)=\frac{\|\nabla f(x)\|^2}{\langle \nabla^2 f(x)\nabla f(x),\nabla f(x)\rangle}.
--   $$
--   3. The iterates of the **gradient method (6.1)** started at $x_0$:
--   $$
--   x_{j+1}=x_j-\gamma(x_j)\,\nabla f(x_j),\qquad j=0,1,2,\dots
--   $$
--   4. For a damping factor $\sigma$, the iterates of the **damped method**, in which $\gamma_j$ is replaced by $\sigma\gamma_j$:
--   $$
--   x_{j+1}=x_j-\sigma\gamma(x_j)\,\nabla f(x_j).
--   $$
--
--   The step $\gamma(x)$ is the exact minimizer of the second-order Taylor model of $f$ along $-\nabla f(x)$. For a quadratic function the method is the steepest descent with exact line search. The step needs one Hessian–vector product per iteration and no knowledge of the smoothness or convexity constants.
--
--   **Formalization Note** The Hessian quadratic form is `fderiv ℝ (fderiv ℝ f) x v v`. Where $f$ is not twice differentiable it takes Lean's default value $0$; every theorem of the mission assumes $f$ and its derivative are differentiable everywhere. At a stationary point ($\nabla f(x)=0$) the step is $0/0$, which Lean evaluates to $0$, so the iterate stays at $x$. For a strongly convex $f$ a stationary point is the minimizer, so the method has stopped there, which is the only sensible reading of (6.1).
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 13, Eq. (6.1) and the damped version (γ_j replaced with σγ_j) stated in Theorem 6.1

import Mathlib

namespace FatkhullinPolyak.HessStep

/-- The Hessian quadratic form `⟨∇²f(x) v, v⟩`, read off the second Fréchet derivative:
`fderiv ℝ (fderiv ℝ f) x` is the Hessian of `f` at `x` as a bilinear map, applied to `(v, v)`.
Where `f` is not twice differentiable at `x` this is Lean's junk value `0`; every statement of
the mission assumes `f` and `fderiv ℝ f` differentiable everywhere. -/
noncomputable def hessQuad {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x v v

/-- The step size of the method (6.1) at the point `x`:
`γ(x) = ‖∇f(x)‖² / ⟨∇²f(x)∇f(x), ∇f(x)⟩`. At a stationary point both numerator and
denominator vanish and Lean's division gives `γ(x) = 0`, so the method stays put. -/
noncomputable def hessStep {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖gradient f x‖ ^ 2 / hessQuad f x (gradient f x)

/-- The iterates of the gradient method (6.1) with the Hessian step size, started at `x₀`:
`x_{j+1} = x_j − γ(x_j) ∇f(x_j)`. -/
noncomputable def hessIter {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | j + 1 => hessIter f x₀ j - hessStep f (hessIter f x₀ j) • gradient f (hessIter f x₀ j)

/-- The iterates of the damped version of (6.1), with `γ_j` replaced by `σ γ_j`, started at
`x₀`: `x_{j+1} = x_j − σ γ(x_j) ∇f(x_j)`. -/
noncomputable def dampedHessIter {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (σ : ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x₀
  | j + 1 => dampedHessIter f σ x₀ j -
      (σ * hessStep f (dampedHessIter f σ x₀ j)) • gradient f (dampedHessIter f σ x₀ j)

end FatkhullinPolyak.HessStep


