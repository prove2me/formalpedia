-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP3Z
-- name    : DiscreteConvex_NetworkFlowsB_FeasibleFlowMSFP3Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:58.353444+00:00
-- url     : https://prove2.me/theorems/131fc131-34ce-47c2-b737-acd8170a5b8b
-- title:
--   FeasibleFlowMSFP3Z
-- statement:
--   Feasibility for the M-convex submodular integer-flow problem MSFP3.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.257-258, integer-flow version of Eqs. (9.47)-(9.48).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.257-258, integer-flow version of Eqs. (9.47)-(9.48)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for the M-convex submodular integer-flow problem MSFP3. -/
def FeasibleFlowMSFP3Z (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ)
    (xi : A → ℤ) : Prop :=
  (∀ a : A, fa a (xi a) ≠ ⊤) ∧ f (BoundaryZ tail head xi) ≠ ⊤

end DiscreteConvex.NetworkFlowsB


