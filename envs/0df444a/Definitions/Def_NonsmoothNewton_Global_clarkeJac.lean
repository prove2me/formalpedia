-- Prove2me | Definitions.Def_NonsmoothNewton_Global_clarkeJac
-- name    : NonsmoothNewton_Global_clarkeJac
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:06:22.198187+00:00
-- url     : https://prove2.me/theorems/8ec86759-8750-4581-9c9f-e252dcf7d70d
-- title:
--   Clarke generalized Jacobian $\partial F(x)=\mathrm{co}\{\lim JF(x_i): x_i\to x,\ x_i\in D_F\}$ (2.1)
-- statement:
--   Let $E$ and $G$ be finite-dimensional real normed spaces and $F : E \to G$. Write $D_F$ for the set of points at which $F$ is (Fréchet) differentiable and $JF(y)$ for the derivative of $F$ at $y \in D_F$.
--
--   1. The **B-limit set** of $F$ at $x$ is the set of all linear maps $V : E \to G$ that arise as limits $V = \lim_{i\to\infty} JF(x_i)$ along some sequence $x_i \to x$ with $x_i \in D_F$.
--   2. **Clarke's generalized Jacobian** of $F$ at $x$ is the convex hull of the B-limit set:
--
--   $$
--   \partial F(x) = \mathrm{co}\Big\{ \lim_{x_i \to x,\ x_i \in D_F} JF(x_i) \Big\}.
--   $$
--
--   For a locally Lipschitz $F$ on $\mathbb{R}^n$, Rademacher's theorem makes $D_F$ of full measure, and $\partial F(x)$ is a nonempty compact convex set of linear maps; for $C^1$ maps it reduces to $\{JF(x)\}$. It is the set of "slopes" used by the nonsmooth Newton method $x^{k+1} = x^k - V_k^{-1}F(x^k)$, $V_k \in \partial F(x^k)$.
--
--   **Formalization Note** Derivatives are Mathlib's `fderiv`, a continuous linear map, in place of the Jacobian matrix. Limits are taken along sequences; the sequence may hit $x$ itself. No closure is taken after the convex hull: for locally Lipschitz $F$ the B-limit set is compact in finite dimension, so its convex hull is already closed.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 354, Section 2, Eq. (2.1)

import Mathlib

namespace NonsmoothNewton.Global

open Filter Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- The differentiability set `D_F = {y | F is differentiable at y}` (Qi–Sun 1993, p. 354). -/
def diffSet (F : E → G) : Set E := {y | DifferentiableAt ℝ F y}

/-- The B-limit set: all limits `lim JF(x_i)` of derivatives along sequences `x_i → x` with
`x_i ∈ D_F` (Qi–Sun 1993, p. 354, inside Eq. (2.1)). -/
def bJac (F : E → G) (x : E) : Set (E →L[ℝ] G) :=
  {V | ∃ u : ℕ → E, Tendsto u atTop (𝓝 x) ∧ (∀ k, DifferentiableAt ℝ F (u k)) ∧
    Tendsto (fun k => fderiv ℝ F (u k)) atTop (𝓝 V)}

/-- Clarke's generalized Jacobian `∂F(x) = co{lim_{x_i → x, x_i ∈ D_F} JF(x_i)}`
(Qi–Sun 1993, p. 354, Eq. (2.1)): the convex hull of the B-limit set. -/
def clarkeJac (F : E → G) (x : E) : Set (E →L[ℝ] G) :=
  convexHull ℝ (bJac F x)

end NonsmoothNewton.Global


