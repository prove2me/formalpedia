-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeROnT
-- name    : DiscreteConvex_NetworkFlowsC_InducedFTildeROnT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:10:52.811739+00:00
-- url     : https://prove2.me/theorems/09d1bb05-1d74-4f00-8bc7-1f3cc3b1ec17
-- title:
--   The real induced flow-type function on the terminal set
-- statement:
--   The real-domain induced function $\tilde f$ read **as a function on $\mathbb{R}^T$**, which is what Theorem 9.28 asserts is M-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Theorem 9.28.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Theorem 9.28

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeRWT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ExtendFromTR

namespace DiscreteConvex.NetworkFlowsC

open Classical
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The real-domain induced function `f̃` as a function **on `Rᵀ`**, which is what Theorem 9.28
asserts is M-convex; read on all of `Rⱽ` it is a cylinder along `V ∖ T`. -/
noncomputable def InducedFTildeROnT (tail head : A → V) (S T : Finset V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (y : {v // v ∈ T} → ℝ) : WithTop ℝ :=
  InducedFTildeRWT tail head S T fa f (ExtendFromTR T y)

end DiscreteConvex.NetworkFlowsC


