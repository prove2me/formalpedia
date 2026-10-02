-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxHeadMSFP2
-- name    : DiscreteConvex_NetworkFlowsC_AuxHeadMSFP2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:39.476229+00:00
-- url     : https://prove2.me/theorems/a274c810-7f31-4515-af4a-6ba626705448
-- title:
--   AuxHeadMSFP2
-- statement:
--   The head map of the MSFP2 auxiliary network.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def AuxHeadMSFP2 (tail head : A → V) : A ⊕ A ⊕ (V × V) → V
  | .inl a => head a
  | .inr (.inl a) => tail a
  | .inr (.inr (_, v)) => v

end DiscreteConvex.NetworkFlowsC


