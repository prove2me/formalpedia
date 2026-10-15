-- Prove2me | Definitions.Def_ZORiem_RGD_rgrad
-- name    : ZORiem_RGD_rgrad
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:28.2119+00:00
-- url     : https://prove2.me/theorems/6b5db233-b491-4b23-9350-e176a8276fa8
-- title:
--   (2.3), p. 7 — Riemannian gradient grad f(x) = Proj_{TₓM}(∇f(x)) for the induced metric
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $M\subseteq E$, and $f:E\to\mathbb R$. Equip $M$ with the Riemannian metric induced by the inner product of $E$. The **Riemannian gradient** of $f$ at $x$ is the orthogonal projection of the Euclidean gradient onto the tangent space $T_xM$:
--
--   $$\operatorname{grad} f(x)=\operatorname{Proj}_{T_xM}\big(\nabla f(x)\big).$$
--
--   This is display (2.3) of the paper; all of its first-order estimates are stated in terms of $\operatorname{grad} f$.
--
--   **Formalization Note** $\nabla f(x)$ is Mathlib's `gradient f x` and the projection is `(tangentSpace M x).starProjection`. The `gradient` of a function that is not differentiable at $x$ is $0$, so every theorem using `rgrad` assumes $f$ differentiable.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, (2.3), p. 7

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ZORiem.RGD

open ProjLikeRetr.Retractor

/-- (2.3), p. 7: the Riemannian gradient of `f` at `x` for the metric induced by the Euclidean inner
product, `grad f(x) = Proj_{T_xM}(∇f(x))`, the orthogonal projection of the Euclidean gradient onto
the tangent space `T_xM`. -/
noncomputable def rgrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (f : E → ℝ) (x : E) : E :=
  (tangentSpace M x).starProjection (gradient f x)

end ZORiem.RGD


