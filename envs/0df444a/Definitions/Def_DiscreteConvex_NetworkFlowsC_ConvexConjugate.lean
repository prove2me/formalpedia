-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugate
-- name    : DiscreteConvex_NetworkFlowsC_ConvexConjugate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:07.355657+00:00
-- url     : https://prove2.me/theorems/dbeea350-7739-4c56-813f-d311604043cd
-- title:
--   ConvexConjugate
-- statement:
--   The discrete Legendre-Fenchel transform, integer domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Eq. (8.11), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The discrete Legendre-Fenchel transform, integer domain. -/
noncomputable def ConvexConjugate (f : (V → ℤ) → WithTop ℝ) (p : V → ℤ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ x : V → ℤ,
    v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x)})

end DiscreteConvex.NetworkFlowsC


