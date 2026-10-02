-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxTailMSFP2
-- name    : DiscreteConvex_NetworkFlowsB_AuxTailMSFP2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:44.792646+00:00
-- url     : https://prove2.me/theorems/cf6fb8d6-edf0-4386-9dc8-3911b533ae3f
-- title:
--   AuxTailMSFP2
-- statement:
--   The tail map of the MSFP2 auxiliary network, on $A_\xi=A^*_\xi\oplus B^*_\xi\oplus C_\xi$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The tail map of the MSFP2 auxiliary network, on `Aξ = A*ξ ⊕ B*ξ ⊕ Cξ`. -/
def AuxTailMSFP2 (tail head : A → V) : A ⊕ A ⊕ (V × V) → V
  | .inl a => tail a
  | .inr (.inl a) => head a
  | .inr (.inr (u, _)) => u

end DiscreteConvex.NetworkFlowsB


