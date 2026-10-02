-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMSFP3
-- name    : DiscreteConvex_NetworkFlowsB_OptimalPotentialSetMSFP3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:27:57.021012+00:00
-- url     : https://prove2.me/theorems/674ac2c6-57ff-4ab8-bf40-fdfbfa20af45
-- title:
--   OptimalPotentialSetMSFP3
-- statement:
--   The set of optimal potentials for MSFP3, $\Pi^*=\{p:p\text{ optimal potential}\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.261

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMCFP3
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsOptimalPotential

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of optimal potentials for MSFP3, `Π* = {p | p optimal potential}`. -/
def OptimalPotentialSetMSFP3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) :=
  {p | ∃ xi, OptimalFlowMCFP3 tail head fa f xi ∧ IsOptimalPotential tail head fa f xi p}

-- ===== MCFP0 (linear arc cost, as a special case of MCFP3, Eq. (9.11)) =====

end DiscreteConvex.NetworkFlowsB


