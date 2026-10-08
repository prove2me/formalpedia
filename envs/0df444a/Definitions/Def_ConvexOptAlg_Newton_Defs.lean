-- Prove2me | Definitions.Def_ConvexOptAlg_Newton_Defs
-- name    : ConvexOptAlg_Newton_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:16:30.589631+00:00
-- url     : https://prove2.me/theorems/6c0b9a87-d246-4aed-9af2-1d95cc4e0ae6
-- title:
--   §5.3.2, p. 320 — C² function with gradient and Hessian maps, Lipschitz Hessian, and Newton's method x_{k+1} = x_k − [∇²f(x_k)]⁻¹∇f(x_k)
-- statement:
--   Throughout, $\mathbb R^n$ carries the Euclidean norm $\|\cdot\|$, and $\|A\|$ denotes the operator norm of a linear map $A:\mathbb R^n\to\mathbb R^n$, so that $\|Ax\|\le\|A\|\,\|x\|$.
--
--   **C² function, gradient and Hessian.** A function $f:\mathbb R^n\to\mathbb R$ is twice continuously differentiable, with gradient $\nabla f:\mathbb R^n\to\mathbb R^n$ and Hessian $\nabla^2 f:\mathbb R^n\to L(\mathbb R^n,\mathbb R^n)$, where $\nabla^2 f(x)$ is the derivative of the gradient map at $x$.
--
--   **Lipschitz Hessian.** For $M\in\mathbb R$, the Hessian is $M$-Lipschitz if
--
--   $$\|\nabla^2 f(x)-\nabla^2 f(y)\|\le M\,\|x-y\|\qquad\text{for all }x,y\in\mathbb R^n.$$
--
--   **Newton's method.** Starting at $x_0\in\mathbb R^n$, Newton's method iterates, for $k\ge 0$,
--
--   $$x_{k+1}=x_k-[\nabla^2 f(x_k)]^{-1}\nabla f(x_k).$$
--
--   These are the objects of the traditional local analysis of Newton's method: the method itself and the regularity assumption (a Lipschitz Hessian) under which it converges quadratically near a strict local minimum.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The gradient and the Hessian are explicit maps $g$ and $H$ with $g(x)=\nabla f(x)$ (`HasGradientAt`) and $H(x)$ the Fréchet derivative of $g$ at $x$ (`HasFDerivAt`), together with `ContDiff ℝ 2 f`. A Newton run is a sequence $x:\mathbb N\to\mathbb R^n$ satisfying the linear system $\nabla^2 f(x_k)(x_k-x_{k+1})=\nabla f(x_k)$ for every $k\ge 0$: this is the printed recursion whenever $\nabla^2 f(x_k)$ is invertible, and it never takes the inverse of a possibly singular operator (Lean's inverse of a non-invertible map is $0$). Invertibility along the run is a conclusion of Theorem 5.3, not part of the definition.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, arXiv:1405.4980v2, §5.3.2, p. 320 (C² f, operator norm, Newton's method) and Theorem 5.3, p. 320 (Lipschitz Hessian)

import Mathlib

namespace ConvexOptAlg.Newton

open InnerProductSpace

/-- `f : ℝⁿ → ℝ` is a C² function whose gradient map is `g` and whose Hessian map is `H`
(Bubeck, arXiv:1405.4980v2, §5.3.2, p. 320: "Let f : ℝⁿ → ℝ be a C² function"):
`f` is twice continuously differentiable, `g x = ∇f(x)` for every `x`, and `H x = ∇²f(x)` is the
derivative of the gradient map at every `x`. The Hessian is a continuous linear map
`ℝⁿ →L[ℝ] ℝⁿ`; its norm is the operator norm, as on the page. -/
def IsC2GradHess {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :
    Prop :=
  ContDiff ℝ 2 f ∧ (∀ x, HasGradientAt f (g x) x) ∧ ∀ x, HasFDerivAt g (H x) x

/-- The Hessian map `H` is `M`-Lipschitz in operator norm (Bubeck, arXiv:1405.4980v2,
Theorem 5.3, p. 320): `‖∇²f(x) − ∇²f(y)‖ ≤ M‖x − y‖` for all `x, y ∈ ℝⁿ`. -/
def IsLipschitzHessian {n : ℕ}
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (M : ℝ) : Prop :=
  ∀ x y, ‖H x - H y‖ ≤ M * ‖x - y‖

/-- A run of Newton's method (Bubeck, arXiv:1405.4980v2, §5.3.2, p. 320):
`x_{k+1} = x_k − [∇²f(x_k)]⁻¹ ∇f(x_k)` for every `k ≥ 0`, starting at `x₀ = x 0`.
The step is encoded as the linear system it solves, `∇²f(x_k)(x_k − x_{k+1}) = ∇f(x_k)`, so no
inverse of a possibly singular operator is ever taken. When every `∇²f(x_k)` is invertible the
relation determines `x_{k+1}` uniquely and coincides with the printed formula; that the Hessians
along the run are invertible ("Newton's method is well-defined") is a conclusion of Theorem 5.3,
not part of this definition. -/
def IsNewtonRun {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k : ℕ, H (x k) (x k - x (k + 1)) = g (x k)

end ConvexOptAlg.Newton


