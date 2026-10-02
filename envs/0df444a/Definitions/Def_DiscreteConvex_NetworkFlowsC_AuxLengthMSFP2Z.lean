-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxLengthMSFP2Z
-- name    : DiscreteConvex_NetworkFlowsC_AuxLengthMSFP2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:54:07.88558+00:00
-- url     : https://prove2.me/theorems/65f1c0f2-b09c-45b4-8369-e5ee31ab1fa3
-- title:
--   AuxLengthMSFP2Z
-- statement:
--   The arc-length function $\ell_\xi$, integer flows.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Eq. (9.74), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Eq. (9.74), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DeltaF

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def AuxLengthMSFP2Z (tail head : A → V) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) :
    A ⊕ A ⊕ (V × V) → WithTop ℝ
  | .inl a => (gamma a : WithTop ℝ)
  | .inr (.inl a) => ((-gamma a : ℝ) : WithTop ℝ)
  | .inr (.inr (u, v)) => DeltaF f (BoundaryZ tail head xi) v u

end DiscreteConvex.NetworkFlowsC


