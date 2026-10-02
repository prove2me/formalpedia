-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeRWT
-- name    : DiscreteConvex_NetworkFlowsC_InducedFTildeRWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:34.026977+00:00
-- url     : https://prove2.me/theorems/2d8c2da8-c1fc-446c-9f44-3d05b3e8ab5e
-- title:
--   InducedFTildeRWT
-- statement:
--   $\tilde f$ projected to $\mathbb R\cup\{+\infty\}$, real domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, projected, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, projected, real version

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedFTildeRWT (tail head : A → V) (S T : Finset V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (y : V → ℝ) : WithTop ℝ :=
  FromEReal (InducedFTildeR tail head S T fa f y)

end DiscreteConvex.NetworkFlowsC


