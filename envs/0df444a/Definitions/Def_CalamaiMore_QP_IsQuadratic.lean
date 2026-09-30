-- Prove2me | Definitions.Def_CalamaiMore_QP_IsQuadratic
-- name    : CalamaiMore_QP_IsQuadratic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:57:28.812442+00:00
-- url     : https://prove2.me/theorems/fb7c9ed5-0115-4cf1-9528-3f57aa4488be
-- title:
--   Quadratic function $f(x) = \tfrac12\langle x, Qx\rangle + \langle b, x\rangle + c_0$
-- statement:
--   Let $E$ be a real inner product space. A function $f : E \to \mathbb{R}$ is **quadratic** if there are a self-adjoint (symmetric) linear map $Q : E \to E$, a vector $b \in E$ and a scalar $c_0 \in \mathbb{R}$ such that
--
--   $$
--   f(x) = \tfrac12 \langle x, Qx \rangle + \langle b, x \rangle + c_0 \qquad \text{for all } x \in E.
--   $$
--
--   No definiteness is imposed on $Q$: convex, concave and indefinite quadratics are all included, as in Section 6 of Calamai and Moré, which treats indefinite Hessians explicitly. The gradient of such an $f$ is $\nabla f(x) = Qx + b$ and its Hessian is $Q$.
--
--   **Formalization Note** The paper uses "quadratic function $f : \mathbb{R}^n \to \mathbb{R}$" without a formal definition; this is the standard one. Requiring $Q$ symmetric loses no generality, since $\langle x, Qx\rangle$ only depends on the symmetric part of $Q$.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), pp. 110–111, §6 (quadratic function f, Algorithm 6.1, Theorem 6.2)

import Mathlib

namespace CalamaiMore.QP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `f` is a quadratic function: `f(x) = ½ ⟨x, Q x⟩ + ⟨b, x⟩ + c₀` for some self-adjoint
(symmetric) linear map `Q` of `E`, some `b ∈ E` and some `c₀ ∈ ℝ`. `Q` is not required to be
positive semidefinite, so indefinite quadratics are included. -/
def IsQuadratic (f : E → ℝ) : Prop :=
  ∃ (Q : E →ₗ[ℝ] E) (b : E) (c₀ : ℝ), Q.IsSymmetric ∧
    ∀ x : E, f x = (1 / 2 : ℝ) * inner ℝ x (Q x) + inner ℝ b x + c₀

end CalamaiMore.QP


