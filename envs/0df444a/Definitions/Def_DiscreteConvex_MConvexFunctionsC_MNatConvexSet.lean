-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatConvexSet
-- name    : DiscreteConvex_MConvexFunctionsC_MNatConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:29:22.065717+00:00
-- url     : https://prove2.me/theorems/ee470698-0264-4634-9bb8-dee620795f7d
-- title:
--   MNatConvexSet
-- statement:
--   $D \subseteq \mathbb Z^V$ is an M$^\natural$-convex set: its lift is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ExchangeAxiomB
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_LiftedSet

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
def MNatConvexSet (D : Set (V → ℤ)) : Prop := ExchangeAxiomB (LiftedSet D)

end DiscreteConvex.MConvexFunctionsC


