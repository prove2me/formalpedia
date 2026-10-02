-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxTailMSFP2
-- name    : DiscreteConvex_NetworkFlowsC_AuxTailMSFP2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:49:37.868992+00:00
-- url     : https://prove2.me/theorems/630aa3dc-7bb4-44a0-bcbe-afd1cd7e7c2c
-- title:
--   AuxTailMSFP2
-- statement:
--   The tail map of the MSFP2 auxiliary network.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70), redeclared

import Mathlib

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def AuxTailMSFP2 (tail head : A → V) : A ⊕ A ⊕ (V × V) → V
  | .inl a => tail a
  | .inr (.inl a) => head a
  | .inr (.inr (u, _)) => u

end DiscreteConvex.NetworkFlowsC


