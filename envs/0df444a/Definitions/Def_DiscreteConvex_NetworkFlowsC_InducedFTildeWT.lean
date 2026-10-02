-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeWT
-- name    : DiscreteConvex_NetworkFlowsC_InducedFTildeWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:05.480916+00:00
-- url     : https://prove2.me/theorems/fffdc4cb-3333-43db-b2d8-0d03972dc5e6
-- title:
--   InducedFTildeWT
-- statement:
--   $\tilde f$ projected to $\mathbb R\cup\{+\infty\}$ (assuming properness).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.81), projected.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.81), projected

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTilde

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedFTildeWT (tail head : A → V) (S T : Finset V) (fa : A → ℤ → WithTop ℝ)
    (f : (V → ℤ) → WithTop ℝ) (y : V → ℤ) : WithTop ℝ :=
  FromEReal (InducedFTilde tail head S T fa f y)

end DiscreteConvex.NetworkFlowsC


