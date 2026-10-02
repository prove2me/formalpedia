-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeROnT
-- name    : DiscreteConvex_NetworkFlowsC_InducedGTildeROnT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:11:11.397613+00:00
-- url     : https://prove2.me/theorems/9c0b53be-388c-49d1-b06c-be63d7f55428
-- title:
--   The real induced potential-type function on the terminal set
-- statement:
--   The real-domain induced function $\tilde g$ read **as a function on $\mathbb{R}^T$**, which is what Theorem 9.28 asserts is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Theorem 9.28.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Theorem 9.28

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeRWT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ExtendFromTR

namespace DiscreteConvex.NetworkFlowsC

open Classical
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The real-domain induced function `g̃` as a function **on `Rᵀ`**, which is what Theorem 9.28
asserts is L-convex; read on all of `Rⱽ` it is a cylinder along `V ∖ T`. -/
noncomputable def InducedGTildeROnT (tail head : A → V) (S T : Finset V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (y : {v // v ∈ T} → ℝ) : WithTop ℝ :=
  InducedGTildeRWT tail head S T fa f (ExtendFromTR T y)

end DiscreteConvex.NetworkFlowsC


