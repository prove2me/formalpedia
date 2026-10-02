-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxLengthMSFP2Z
-- name    : DiscreteConvex_NetworkFlowsB_AuxLengthMSFP2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:24:36.991057+00:00
-- url     : https://prove2.me/theorems/38738b93-c8e8-4e5d-8acb-f905e2912acb
-- title:
--   AuxLengthMSFP2Z
-- statement:
--   The arc-length function $\ell_\xi$ of Eq. (9.74), integer flows.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Eq. (9.74).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Eq. (9.74)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_DeltaF

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The arc-length function `ℓξ` of Eq. (9.74), integer flows. -/
def AuxLengthMSFP2Z (tail head : A → V) (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) :
    A ⊕ A ⊕ (V × V) → WithTop ℝ
  | .inl a => (gamma a : WithTop ℝ)
  | .inr (.inl a) => ((-gamma a : ℝ) : WithTop ℝ)
  | .inr (.inr (u, v)) => DeltaF f (BoundaryZ tail head xi) v u

-- ===== Theorems =====

end DiscreteConvex.NetworkFlowsB


