-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeOnT
-- name    : DiscreteConvex_NetworkFlowsC_InducedGTildeOnT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:10:48.643388+00:00
-- url     : https://prove2.me/theorems/e19b210e-4a04-4d97-a8b6-9f8e9a5473f7
-- title:
--   The induced potential-type function on the terminal set
-- statement:
--   The induced function $\tilde g$ of Eq. (9.82) read **as a function on $\mathbb{Z}^T$**, which is what Theorems 9.26 and 9.27 assert is L-convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Eq. (9.82).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Eq. (9.82)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeWT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ExtendFromT

namespace DiscreteConvex.NetworkFlowsC

open Classical
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The induced function `g̃` of Eq. (9.82) as a function **on `Zᵀ`**, which is what Theorems
9.26 and 9.27 assert is L-convex; `InducedGTildeWT` reads the same value off a vector of `Zⱽ` and
is therefore a cylinder along `V ∖ T`. -/
noncomputable def InducedGTildeOnT (tail head : A → V) (S T : Finset V) (fa : A → ℤ → WithTop ℝ)
    (f : (V → ℤ) → WithTop ℝ) (y : {v // v ∈ T} → ℤ) : WithTop ℝ :=
  InducedGTildeWT tail head S T fa f (ExtendFromT T y)

end DiscreteConvex.NetworkFlowsC


