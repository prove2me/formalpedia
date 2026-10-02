-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
-- name    : DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:25:25.455632+00:00
-- url     : https://prove2.me/theorems/1d6a2362-e2d3-4ce0-8a71-f814405a9654
-- title:
--   OptimalFlowMCFP3
-- statement:
--   $\xi$ is an optimal flow for MCFP3 / MSFP3.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246-247, adjacent to Eqs. (9.7)-(9.10).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246-247, adjacent to Eqs. (9.7)-(9.10)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Gamma3

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- `ξ` is an optimal flow for MCFP3 / MSFP3. -/
def OptimalFlowMCFP3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) : Prop :=
  FeasibleFlowMCFP3 tail head fa f xi ∧
    ∀ xi', FeasibleFlowMCFP3 tail head fa f xi' → Gamma3 tail head fa f xi ≤ Gamma3 tail head fa f xi'

end DiscreteConvex.NetworkFlowsB


