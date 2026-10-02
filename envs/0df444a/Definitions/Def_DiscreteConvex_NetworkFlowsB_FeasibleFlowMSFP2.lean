-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2
-- name    : DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP2
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:47.622154+00:00
-- url     : https://prove2.me/theorems/c5173dcf-7071-4b8a-bd86-b5ba9bb8af76
-- title:
--   FeasibleFlowMSFP2
-- statement:
--   Feasibility for the M-convex submodular flow problem MSFP2.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.256, Eqs. (9.43)-(9.44).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.256, Eqs. (9.43)-(9.44)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for the M-convex submodular flow problem MSFP2. -/
def FeasibleFlowMSFP2 (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (f : (V → ℝ) → WithTop ℝ) (xi : A → ℝ) : Prop :=
  (∀ a : A, cLower a ≤ (xi a : WithBot ℝ) ∧ (xi a : WithTop ℝ) ≤ cUpper a) ∧
    f (Boundary tail head xi) ≠ ⊤

end DiscreteConvex.NetworkFlowsB


