-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP2Z
-- name    : DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:27:16.139159+00:00
-- url     : https://prove2.me/theorems/6f5a80d8-8677-4cec-9f1c-8b23856f74b8
-- title:
--   OptimalFlowMSFP2Z
-- statement:
--   $\xi$ is an optimal integer flow for MSFP2.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, integer-flow version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, integer-flow version

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma2Z

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ξ` is an optimal integer flow for MSFP2. -/
def OptimalFlowMSFP2Z (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) : Prop :=
  FeasibleFlowMSFP2Z tail head cUpper cLower f xi ∧
    ∀ xi', FeasibleFlowMSFP2Z tail head cUpper cLower f xi' →
      Gamma2Z tail head gamma f xi ≤ Gamma2Z tail head gamma f xi'

end DiscreteConvex.NetworkFlowsB


