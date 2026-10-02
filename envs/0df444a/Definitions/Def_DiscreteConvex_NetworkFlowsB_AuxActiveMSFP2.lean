-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_AuxActiveMSFP2
-- name    : DiscreteConvex_NetworkFlowsB_AuxActiveMSFP2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:24:00.368969+00:00
-- url     : https://prove2.me/theorems/af474f40-16f7-42cb-a020-bf32eb974464
-- title:
--   AuxActiveMSFP2
-- statement:
--   Membership in $A_\xi=A^*_\xi\cup B^*_\xi\cup C_\xi$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.263, Eq. (9.70)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Membership in `Aξ = A*ξ ∪ B*ξ ∪ Cξ` (Eq. (9.70)). -/
def AuxActiveMSFP2 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) : A ⊕ A ⊕ (V × V) → Prop
  | .inl a => (xi a : WithTop ℝ) < cUpper a
  | .inr (.inl a) => cLower a < (xi a : WithBot ℝ)
  | .inr (.inr (u, v)) => u ≠ v ∧ ∃ alpha : ℝ, 0 < alpha ∧
      f (fun w => Boundary tail head xi w -
        alpha * ((if w = u then (1:ℝ) else 0) - (if w = v then (1:ℝ) else 0))) ≠ ⊤

end DiscreteConvex.NetworkFlowsB


