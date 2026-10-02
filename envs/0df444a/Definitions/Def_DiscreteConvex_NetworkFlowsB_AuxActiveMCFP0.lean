-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMCFP0
-- name    : DiscreteConvex_NetworkFlowsB_AuxActiveMCFP0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:21:30.062773+00:00
-- url     : https://prove2.me/theorems/465f3c9f-3508-45e1-a7eb-313af352eabd
-- title:
--   AuxActiveMCFP0
-- statement:
--   Membership in $A_\xi=A^*_\xi\cup B^*_\xi$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251, preceding Eq. (9.34).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.251, preceding Eq. (9.34)

import Mathlib

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Membership in `Aξ = A*ξ ∪ B*ξ` (Eq. before (9.34)). -/
def AuxActiveMCFP0 (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (xi : A → ℝ) : A ⊕ A → Prop
  | .inl a => (xi a : WithTop ℝ) < cUpper a
  | .inr a => cLower a < (xi a : WithBot ℝ)

end DiscreteConvex.NetworkFlowsB


