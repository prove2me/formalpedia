-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeOnT
-- name    : DiscreteConvex_NetworkFlowsC_InducedFTildeOnT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:09:59.137359+00:00
-- url     : https://prove2.me/theorems/5c0e74a2-0ab3-43f4-b368-dbc51f0613c1
-- title:
--   The induced flow-type function on the terminal set
-- statement:
--   The induced function $\tilde f$ of Eq. (9.81) read **as a function on $\mathbb{Z}^T$**, which is what Theorems 9.26 and 9.27 assert is M-convex.
--
--   Read instead on all of $\mathbb{Z}^V$ it is a cylinder along $V\setminus T$, for which the exchange axiom fails whenever $T\ne V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Eq. (9.81).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.6, Eq. (9.81)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeWT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ExtendFromT

namespace DiscreteConvex.NetworkFlowsC

open Classical
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The induced function `f̃` of Eq. (9.81) as a function **on `Zᵀ`**, which is what Theorems
9.26 and 9.27 assert is M-convex; `InducedFTildeWT` reads the same value off a vector of `Zⱽ` and
is therefore a cylinder along `V ∖ T`, for which the exchange axiom fails whenever `T ≠ V`. -/
noncomputable def InducedFTildeOnT (tail head : A → V) (S T : Finset V) (fa : A → ℤ → WithTop ℝ)
    (f : (V → ℤ) → WithTop ℝ) (y : {v // v ∈ T} → ℤ) : WithTop ℝ :=
  InducedFTildeWT tail head S T fa f (ExtendFromT T y)

end DiscreteConvex.NetworkFlowsC


