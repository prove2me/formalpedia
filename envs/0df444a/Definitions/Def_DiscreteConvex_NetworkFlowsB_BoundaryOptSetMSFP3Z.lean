-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryOptSetMSFP3Z
-- name    : DiscreteConvex_NetworkFlowsB_BoundaryOptSetMSFP3Z
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:27:25.241479+00:00
-- url     : https://prove2.me/theorems/d7f108c9-1cc1-44ec-b84b-fa98f783fe2a
-- title:
--   BoundaryOptSetMSFP3Z
-- statement:
--   The set of boundaries of optimal integer flows for MSFP3.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Theorem 9.16(3).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.262, Theorem 9.16(3)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsB_OptimalFlowMSFP3Z

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The set of boundaries of optimal integer flows for MSFP3. -/
def BoundaryOptSetMSFP3Z (tail head : A → V) (fa : A → ℤ → WithTop ℝ) (f : (V → ℤ) → WithTop ℝ) :
    Set (V → ℤ) :=
  {x | ∃ xi, OptimalFlowMSFP3Z tail head fa f xi ∧ x = BoundaryZ tail head xi}

end DiscreteConvex.NetworkFlowsB


