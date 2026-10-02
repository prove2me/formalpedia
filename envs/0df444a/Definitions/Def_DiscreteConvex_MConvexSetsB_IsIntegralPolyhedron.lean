-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_IsIntegralPolyhedron
-- name    : DiscreteConvex_MConvexSetsB_IsIntegralPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:30.07873+00:00
-- url     : https://prove2.me/theorems/d374300a-5932-442a-8c72-31386a64ddcb
-- title:
--   IsIntegralPolyhedron
-- statement:
--   A polyhedron $P \subseteq \mathbb R^V$ is **integral** if it coincides with the convex hull of the integer points it contains: $P = \operatorname{conv}(P \cap \mathbb Z^V)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90 and p.107 (supporting Proposition 4.6).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90 and p.107 (supporting Proposition 4.6)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90 (the "integral polyhedron" definition
preceding Eq. (3.50), reused at p.107, Eq. (4.30)-adjacent material): a real polyhedron is
integral if it is the convex hull of the integer points it contains, in
`DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- A polyhedron `P ⊆ Rⱽ` is **integral** if it coincides with the convex hull of the integer
points it contains: `P = conv(P ∩ Zⱽ)`, where `Zⱽ` is represented by its real embedding
`\{x : ∀v, ∃k:ℤ, x(v)=k\}`. -/
def IsIntegralPolyhedron {V : Type*} (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.MConvexSetsB


