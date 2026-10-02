-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateR
-- name    : DiscreteConvex_NetworkFlowsC_ConvexConjugateR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:24.445402+00:00
-- url     : https://prove2.me/theorems/52a73ec3-487f-452e-8a24-cbd8c2de28a6
-- title:
--   ConvexConjugateR
-- statement:
--   The real-variable Legendre-Fenchel transform.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.26), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98, Eq. (3.26), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The (real-variable) Legendre-Fenchel transform. -/
noncomputable def ConvexConjugateR (f : (V → ℝ) → WithTop ℝ) (p : V → ℝ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ x : V → ℝ,
    v = ((∑ i, p i * x i : ℝ) : EReal) - ToEReal (f x)})

end DiscreteConvex.NetworkFlowsC


