-- Prove2me | Definitions.Def_TiltedCvx_Supplement_IsHConvex
-- name    : TiltedCvx_Supplement_IsHConvex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:23:45.440799+00:00
-- url     : https://prove2.me/theorems/1534d3d0-ecf3-43a6-9d79-fa5c3e25af06
-- title:
--   $H$–convexity (Definition 7)
-- statement:
--   Let $X$ be a set and $H$ a family of functions $h:X\to\overline{\mathbb R}$. A function $f:X\to\overline{\mathbb R}$ is **$H$–convex** if there is a non-empty set $U\subseteq H$ with
--
--   $$
--   f(x)=\sup_{h\in U}h(x)\qquad\text{for all }x\in X .
--   $$
--
--   For the affine functions on $\mathbb R^d$, the proper $H$–convex functions are exactly the proper lower semicontinuous convex functions.
--
--   **Formalization Note** The supremum is taken in `EReal`.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 7, p.15

import Mathlib

namespace TiltedCvx.Supplement

/-- **`H`–convexity (Definition 7).** Pedramfar–Khanna–Quinn–Aggarwal, arXiv:2611.03472,
Definition 7, p.15: let `X` be a set and `H` a family of functions `h : X → ℝ̄`. A function
`f : X → ℝ̄` is `H`–convex if there is a non-empty set `U ⊆ H` such that
`f(x) = sup_{h ∈ U} h(x)` for all `x ∈ X`.

**Formalization Note** The supremum is taken in `EReal` (complete lattice). -/
def IsHConvex {X : Type*} (H : Set (X → EReal)) (f : X → EReal) : Prop :=
  ∃ U : Set (X → EReal), U ⊆ H ∧ U.Nonempty ∧ ∀ x, f x = ⨆ h ∈ U, h x

end TiltedCvx.Supplement


