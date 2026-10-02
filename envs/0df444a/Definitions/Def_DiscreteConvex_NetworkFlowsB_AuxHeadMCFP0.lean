-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_AuxHeadMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:27.773237+00:00
-- url     : https://prove2.me/theorems/8b19f19c-c4dc-473d-8925-ceb41eeb87f5
-- title:
--   AuxHeadMCFP0
-- statement:
--   The head map of the MCFP0 auxiliary network $G_\xi$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251, Eq. (9.34)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251, Eq. (9.34)-adjacent

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The head map of the MCFP0 auxiliary network `Gξ`. -/
def AuxHeadMCFP0 (tail head : A → V) : A ⊕ A → V
  | .inl a => head a
  | .inr a => tail a

end DiscreteConvex.NetworkFlowsB


