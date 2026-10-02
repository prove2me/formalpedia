-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP3Z
-- name    : DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP3Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:26.316544+00:00
-- url     : https://prove2.me/theorems/acd7cfea-45b5-49b0-9a9a-412812c70150
-- title:
--   OptimalFlowMSFP3Z
-- statement:
--   $\xi$ is an optimal integer flow for MSFP3.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.257-258, integer-flow version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.257-258, integer-flow version

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP3Z
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma3Z

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ξ` is an optimal integer flow for MSFP3. -/
def OptimalFlowMSFP3Z (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ)
    (xi : A → ℤ) : Prop :=
  FeasibleFlowMSFP3Z tail head fa f xi ∧
    ∀ xi', FeasibleFlowMSFP3Z tail head fa f xi' →
      Gamma3Z tail head fa f xi ≤ Gamma3Z tail head fa f xi'

end DiscreteConvex.NetworkFlowsB


