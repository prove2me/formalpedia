-- Prove2me | Definitions.Def_TiltedCvx_IsRelGrad
-- name    : TiltedCvx_IsRelGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:15.68313+00:00
-- url     : https://prove2.me/theorems/f44faf18-aa3f-47fa-bd47-0d9806290c0d
-- title:
--   Gradient relative to the affine hull
-- statement:
--   Let $K\subseteq\mathbb R^d$ and $x\in\operatorname{ri}(K)$. If $f$ is differentiable at $x$ as a function on the affine hull $\operatorname{aff}(K)$, its gradient with respect to $\operatorname{aff}(K)$ is the vector $g$ in the linear subspace parallel to $\operatorname{aff}(K)$ with
--
--   $$
--   f(u)=f(x)+\langle g,u-x\rangle+o(\|u-x\|)\qquad (u\in\operatorname{aff}(K),\ u\to x).
--   $$
--
--   `IsRelGrad f K x g` states that this gradient exists and equals $g$.
--
--   **Formalization Note** The derivative is taken within `affineSpan ℝ K` of the real function $u\mapsto f(u)$; near $x\in\operatorname{ri}(K)$ with $K=\operatorname{dom}f$ the affine hull lies in $K$, so only finite values are read.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, §3, p.10; Theorem 8(v), p.20

import Mathlib

namespace TiltedCvx

/-- **Gradient relative to the affine hull.** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
§3, p.10 and Theorem 8(v), p.20: if `f` is differentiable at `x ∈ ri(K)` as a function on
`aff(K)`, its gradient with respect to `aff(K)` is the vector in the linear subspace parallel to
`aff(K)` that represents this derivative. `IsRelGrad f K x g` says that this gradient exists and
equals `g`.

**Formalization Note** `g` lies in the direction of `affineSpan ℝ K`, and the real function
`u ↦ (f u).toReal` has derivative `⟨g, ·⟩` at `x` within `aff(K)`. At points `x ∈ ri(K)` with
`K = dom f`, the points of `aff(K)` near `x` lie in `K`, so `toReal` only reads finite values. -/
def IsRelGrad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (K : Set E) (x g : E) : Prop :=
  g ∈ (affineSpan ℝ K).direction ∧
    HasFDerivWithinAt (fun u => (f u).toReal) (innerSL ℝ g) (affineSpan ℝ K : Set E) x

end TiltedCvx


