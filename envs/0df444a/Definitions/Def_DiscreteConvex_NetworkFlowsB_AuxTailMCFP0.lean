-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_AuxTailMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:31.859974+00:00
-- url     : https://prove2.me/theorems/9951f660-e4d5-4350-aef6-b137e498481e
-- title:
--   AuxTailMCFP0
-- statement:
--   The tail map of the MCFP0 auxiliary network $G_\xi$, on $A_\xi=A^*_\xi\oplus B^*_\xi$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251, Eq. (9.34)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251, Eq. (9.34)-adjacent

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The tail map of the MCFP0 auxiliary network `Gξ`, on `Aξ = A*ξ ⊕ B*ξ`. -/
def AuxTailMCFP0 (tail head : A → V) : A ⊕ A → V
  | .inl a => tail a
  | .inr a => head a

end DiscreteConvex.NetworkFlowsB


