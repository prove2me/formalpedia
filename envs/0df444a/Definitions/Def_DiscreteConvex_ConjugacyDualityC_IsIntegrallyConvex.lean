-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_IsIntegrallyConvex
-- name    : DiscreteConvex_ConjugacyDualityC_IsIntegrallyConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:42:19.838066+00:00
-- url     : https://prove2.me/theorems/170ef7a2-b8b1-4d21-8656-7ac29c607dc2
-- title:
--   IsIntegrallyConvex
-- statement:
--   A set $S\subseteq\mathbb Z^V$ is integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100, set version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99-100, set version

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IntEmbed
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_IntegralNeighborhood

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A set `S ⊆ Zⱽ` is integrally convex. -/
def IsIntegrallyConvex (S : Set (V → ℤ)) : Prop :=
  ∀ p : V → ℝ, p ∈ convexHull ℝ (IntEmbed S) →
    p ∈ convexHull ℝ (IntEmbed (S ∩ IntegralNeighborhood p))

end DiscreteConvex.ConjugacyDualityC


