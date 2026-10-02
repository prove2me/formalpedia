-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_AuxActiveMSFP2Z
-- name    : DiscreteConvex_NetworkFlowsC_AuxActiveMSFP2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:54:04.190307+00:00
-- url     : https://prove2.me/theorems/74c9e099-aa25-4ada-bf16-c00aa03d35d8
-- title:
--   AuxActiveMSFP2Z
-- statement:
--   Membership in $A_\xi=A^*_\xi\cup B^*_\xi\cup C_\xi$, integer flows.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Eq. (9.73), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Eq. (9.73), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BoundaryZ

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def AuxActiveMSFP2Z (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) : A ⊕ A ⊕ (V × V) → Prop
  | .inl a => ((xi a : ℝ) : WithTop ℝ) < cUpper a
  | .inr (.inl a) => cLower a < ((xi a : ℝ) : WithBot ℝ)
  | .inr (.inr (u, v)) => u ≠ v ∧
      f (fun w => BoundaryZ tail head xi w + (if w = v then (1:ℤ) else 0) -
        (if w = u then (1:ℤ) else 0)) ≠ ⊤

end DiscreteConvex.NetworkFlowsC


