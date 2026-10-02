-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP2
-- name    : DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:16.405494+00:00
-- url     : https://prove2.me/theorems/396c6b34-aec9-4c63-b118-39d19d6c27f1
-- title:
--   OptimalFlowMSFP2
-- statement:
--   $\xi$ is an optimal flow for MSFP2.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.256, adjacent to Eqs. (9.42)-(9.45).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.256, adjacent to Eqs. (9.42)-(9.45)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma2

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ξ` is an optimal flow for MSFP2. -/
def OptimalFlowMSFP2 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (gamma : A → ℝ) (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) : Prop :=
  FeasibleFlowMSFP2 tail head cUpper cLower f xi ∧
    ∀ xi', FeasibleFlowMSFP2 tail head cUpper cLower f xi' →
      Gamma2 tail head gamma f xi ≤ Gamma2 tail head gamma f xi'

end DiscreteConvex.NetworkFlowsB


