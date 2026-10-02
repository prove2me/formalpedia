-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegralPolyhedron
-- name    : DiscreteConvex_LConvexSetsB_IsIntegralPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:56.918986+00:00
-- url     : https://prove2.me/theorems/ff546496-446e-482e-97bd-c2d95d87d71d
-- title:
--   IsIntegralPolyhedron
-- statement:
--   A polyhedron $P \subseteq \mathbb R^V$ is **integral** if it coincides with the convex hull of the integer points it contains.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90 and p.122 (supporting Proposition 5.1(4)).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90 and p.122 (supporting Proposition 5.1(4))

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90 (the "integral polyhedron"
definition preceding Eq. (3.50), reused at p.122 for Proposition 5.1(4)): a real polyhedron
is integral if it is the convex hull of the integer points it contains, in
`DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- A polyhedron `P ⊆ Rⱽ` is **integral** if it coincides with the convex hull of the
integer points it contains. -/
def IsIntegralPolyhedron {V : Type*} (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.LConvexSetsB


