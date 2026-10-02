-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_IsIntegralPolyhedron
-- name    : DiscreteConvex_MConvexSets_IsIntegralPolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:34.725834+00:00
-- url     : https://prove2.me/theorems/2439f416-2db3-4cc1-8191-1a5134f7b535
-- title:
--   Integral polyhedron
-- statement:
--   A polyhedron $P \subseteq \mathbb R^V$ is **integral** if it coincides with the convex hull of the integer points it contains: $P = \operatorname{conv}(P \cap \mathbb Z^V)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, the definition preceding Eq. (3.50), reused at p.113, Eq. (4.30).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90 and p.113, Eq. (4.30)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90 (the "integral polyhedron" definition
preceding Eq. (3.50), reused at p.113, Eq. (4.30)): a real polyhedron is integral if it is the
convex hull of the integer points it contains, in `DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- A polyhedron `P ⊆ Rⱽ` is **integral** if it coincides with the convex hull of the integer
points it contains: `P = conv(P ∩ Zⱽ)`, where `Zⱽ` is represented by its real embedding
`\{x : ∀v, ∃k:ℤ, x(v)=k\}`. -/
def IsIntegralPolyhedron {V : Type*} (P : Set (V → ℝ)) : Prop :=
  P = convexHull ℝ (P ∩ {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})

end DiscreteConvex.MConvexSets


