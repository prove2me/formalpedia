-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegrallyConvex
-- name    : DiscreteConvex_LConvexSetsB_IsIntegrallyConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:44:30.013498+00:00
-- url     : https://prove2.me/theorems/ccf755e6-7210-4490-b4a6-dd4a8f038a14
-- title:
--   IsIntegrallyConvex
-- statement:
--   A set $S \subseteq \mathbb Z^V$ is **integrally convex** if every point of its convex hull already lies in the convex hull of $S$ restricted to that point's integral neighborhood.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.100, Eq. (3.71)-(3.72), reused p.128.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.100, Eq. (3.71)-(3.72), reused p.128

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntEmbed
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntegralNeighborhood

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.100, Eq. (3.71)-(3.72): integral
convexity of a set, reused at p.128 for Theorem 5.10, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- A set `S ⊆ Zⱽ` is **integrally convex** if every point of its convex hull already lies
in the convex hull of `S` restricted to that point's integral neighborhood. -/
def IsIntegrallyConvex {V : Type*} [Fintype V] (S : Set (V → ℤ)) : Prop :=
  ∀ p : V → ℝ, p ∈ convexHull ℝ (IntEmbed S) →
    p ∈ convexHull ℝ (IntEmbed (S ∩ IntegralNeighborhood p))

end DiscreteConvex.LConvexSetsB


