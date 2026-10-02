-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNatConvexSet
-- name    : DiscreteConvex_MConvexFunctionsB_MNatConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:09:43.600595+00:00
-- url     : https://prove2.me/theorems/c2db3982-2dc5-4e61-b292-a4e855a60d04
-- title:
--   MNatConvexSet
-- statement:
--   $D \subseteq \mathbb Z^V$ is an **M$^\natural$-convex set**: its lift is an M-convex set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, supporting Proposition 6.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.121, supporting Proposition 6.7

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_LiftedSet
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_ExchangeAxiomB

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.121, supporting Proposition 6.7, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- `D ⊆ Zⱽ` is an **M♮-convex set**: its lift is an M-convex set. -/
def MNatConvexSet {V : Type*} [Fintype V] [DecidableEq V] (D : Set (V → ℤ)) : Prop :=
  ExchangeAxiomB (LiftedSet D)

end DiscreteConvex.MConvexFunctionsB


