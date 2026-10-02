-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSets_TriangleInequality
-- name    : DiscreteConvex_LConvexSets_TriangleInequality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:35:16.340792+00:00
-- url     : https://prove2.me/theorems/bbab17e3-6ceb-4520-925b-38891c268df1
-- title:
--   Triangle inequality for a distance function (Eq. 5.2)
-- statement:
--   The **triangle inequality** $\gamma(v_1,v_2) + \gamma(v_2,v_3) \ge \gamma(v_1,v_3)$ for all $v_1,v_2,v_3 \in V$. A distance function satisfying this belongs to the class $T[\mathbb R]$ (or $T[\mathbb Z]$ if additionally integer valued).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.122, Eq. (5.2)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.122, Eq. (5.2): the triangle inequality for a
distance function, in `DiscreteConvex.LConvexSets`.
-/

namespace DiscreteConvex.LConvexSets

/-- The **triangle inequality** (Eq. (5.2)) for `γ : V × V → R ∪ {+∞}`:
`γ(v1,v2) + γ(v2,v3) ≥ γ(v1,v3)` for all `v1, v2, v3 ∈ V`. A distance function satisfying this
belongs to the class `T[R]` (or `T[Z]` if additionally integer valued). -/
def TriangleInequality {V : Type*} (γ : V → V → WithTop ℝ) : Prop :=
  ∀ v1 v2 v3 : V, γ v1 v2 + γ v2 v3 ≥ γ v1 v3

end DiscreteConvex.LConvexSets


