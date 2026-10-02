-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMSFP2Z
-- name    : DiscreteConvex_NetworkFlowsB_AuxActiveMSFP2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:24:18.028532+00:00
-- url     : https://prove2.me/theorems/6430a13f-eb9a-40a5-b022-c4871860f00c
-- title:
--   AuxActiveMSFP2Z
-- statement:
--   Membership in $A_\xi=A^*_\xi\cup B^*_\xi\cup C_\xi$, integer flows.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Eq. (9.73).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, Eq. (9.73)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Membership in `Aξ = A*ξ ∪ B*ξ ∪ Cξ` (Eq. (9.73)), integer flows. -/
def AuxActiveMSFP2Z (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) : A ⊕ A ⊕ (V × V) → Prop
  | .inl a => ((xi a : ℝ) : WithTop ℝ) < cUpper a
  | .inr (.inl a) => cLower a < ((xi a : ℝ) : WithBot ℝ)
  | .inr (.inr (u, v)) => u ≠ v ∧
      f (fun w => BoundaryZ tail head xi w + (if w = v then (1:ℤ) else 0) -
        (if w = u then (1:ℤ) else 0)) ≠ ⊤

end DiscreteConvex.NetworkFlowsB


