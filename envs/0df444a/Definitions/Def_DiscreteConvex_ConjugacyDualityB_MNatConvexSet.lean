-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_MNatConvexSet
-- name    : DiscreteConvex_ConjugacyDualityB_MNatConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:32:43.927732+00:00
-- url     : https://prove2.me/theorems/5029de65-a6e7-4304-8082-83d4d938f438
-- title:
--   MNatConvexSet
-- statement:
--   $D$ is M$^\natural$-convex: its lift is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, set analogue.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.134, set analogue

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_LiftedSet

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- `D` is M♮-convex: its lift is an M-convex set. -/
def MNatConvexSet (D : Set (V → ℤ)) : Prop := ExchangeAxiomB (LiftedSet D)

end DiscreteConvex.ConjugacyDualityB


