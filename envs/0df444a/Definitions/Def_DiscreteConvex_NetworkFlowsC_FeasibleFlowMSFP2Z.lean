-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_FeasibleFlowMSFP2Z
-- name    : DiscreteConvex_NetworkFlowsC_FeasibleFlowMSFP2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:49.449249+00:00
-- url     : https://prove2.me/theorems/a70f30a5-0424-4444-84d9-96c873e0cf35
-- title:
--   FeasibleFlowMSFP2Z
-- statement:
--   Feasibility for the M-convex submodular integer flow problem MSFP2.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BoundaryZ

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
def FeasibleFlowMSFP2Z (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) : Prop :=
  (∀ a : A, cLower a ≤ ((xi a : ℝ) : WithBot ℝ) ∧ ((xi a : ℝ) : WithTop ℝ) ≤ cUpper a) ∧
    f (BoundaryZ tail head xi) ≠ ⊤

end DiscreteConvex.NetworkFlowsC


