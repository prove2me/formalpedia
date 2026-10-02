-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvex
-- name    : DiscreteConvex_ConjugacyDualityB_IsIntegrallyConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:31:10.929861+00:00
-- url     : https://prove2.me/theorems/1e49dc76-4356-4d1d-a67a-bffb1cb8dcbf
-- title:
--   IsIntegrallyConvex
-- statement:
--   A set $S\subseteq\mathbb Z^V$ is integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100, set version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100, set version

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntEmbed
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_IntegralNeighborhood

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A set `S ⊆ Zⱽ` is integrally convex: every point of its convex hull already lies in the
convex hull of `S` restricted to that point's integral neighborhood. -/
def IsIntegrallyConvex (S : Set (V → ℤ)) : Prop :=
  ∀ p : V → ℝ, p ∈ convexHull ℝ (IntEmbed S) →
    p ∈ convexHull ℝ (IntEmbed (S ∩ IntegralNeighborhood p))

end DiscreteConvex.ConjugacyDualityB


