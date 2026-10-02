-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityC_MNatConvexSet
-- name    : DiscreteConvex_ConjugacyDualityC_MNatConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:43:19.478001+00:00
-- url     : https://prove2.me/theorems/a38971af-ed5d-431a-ac8f-161412348d9f
-- title:
--   MNatConvexSet
-- statement:
--   $D$ is M$^\natural$-convex: its lift is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityC_LiftedSet

namespace DiscreteConvex.ConjugacyDualityC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M♮-convex: its lift is an M-convex set. -/
def MNatConvexSet (D : Set (V → ℤ)) : Prop := ExchangeAxiomB (LiftedSet D)

end DiscreteConvex.ConjugacyDualityC


