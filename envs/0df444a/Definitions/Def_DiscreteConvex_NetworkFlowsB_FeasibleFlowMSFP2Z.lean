-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2Z
-- name    : DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:24:03.205438+00:00
-- url     : https://prove2.me/theorems/ff6d1a52-d23c-4ec2-9dee-26054bcfa1b3
-- title:
--   FeasibleFlowMSFP2Z
-- statement:
--   Feasibility for the M-convex submodular integer flow problem MSFP2.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, integer-flow version of Eq. (9.72).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.264, integer-flow version of Eq. (9.72)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for the M-convex submodular integer flow problem MSFP2. -/
def FeasibleFlowMSFP2Z (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℤ) → WithTop ℝ) (xi : A → ℤ) : Prop :=
  (∀ a : A, cLower a ≤ ((xi a : ℝ) : WithBot ℝ) ∧ ((xi a : ℝ) : WithTop ℝ) ≤ cUpper a) ∧
    f (BoundaryZ tail head xi) ≠ ⊤

end DiscreteConvex.NetworkFlowsB


