-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_TriangleInequality
-- name    : DiscreteConvex_LConvexSetsB_TriangleInequality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:24.233984+00:00
-- url     : https://prove2.me/theorems/76149d10-ac8f-424c-a036-8a940583be09
-- title:
--   TriangleInequality
-- statement:
--   The **triangle inequality** (5.2): $\gamma(v_1,v_2)+\gamma(v_2,v_3) \ge \gamma(v_1,v_3)$ for all $v_1,v_2,v_3$. A distance function satisfying this is in the class $T[\mathbb R]$ (or $T[\mathbb Z]$ when additionally integer valued).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.2)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122, Eq. (5.2): the triangle
inequality for a distance function, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- The **triangle inequality** (5.2): `γ(v1,v2) + γ(v2,v3) ≥ γ(v1,v3)` for all
`v1,v2,v3`. A distance function satisfying this is in the class `T[R]` (or `T[Z]` when
additionally integer valued). -/
def TriangleInequality {V : Type*} (γ : V → V → WithTop ℝ) : Prop :=
  ∀ v1 v2 v3, γ v1 v2 + γ v2 v3 ≥ γ v1 v3

end DiscreteConvex.LConvexSetsB


