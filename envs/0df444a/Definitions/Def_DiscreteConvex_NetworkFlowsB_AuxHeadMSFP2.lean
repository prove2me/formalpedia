-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxHeadMSFP2
-- name    : DiscreteConvex_NetworkFlowsB_AuxHeadMSFP2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:46.040185+00:00
-- url     : https://prove2.me/theorems/ed499152-227e-4e8e-bb84-028e855262d4
-- title:
--   AuxHeadMSFP2
-- statement:
--   The head map of the MSFP2 auxiliary network.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The head map of the MSFP2 auxiliary network. -/
def AuxHeadMSFP2 (tail head : A → V) : A ⊕ A ⊕ (V × V) → V
  | .inl a => head a
  | .inr (.inl a) => tail a
  | .inr (.inr (_, v)) => v

end DiscreteConvex.NetworkFlowsB


