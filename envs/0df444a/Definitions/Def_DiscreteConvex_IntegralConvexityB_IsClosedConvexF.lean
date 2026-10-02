-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsClosedConvexF
-- name    : DiscreteConvex_IntegralConvexityB_IsClosedConvexF
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:04:00.936431+00:00
-- url     : https://prove2.me/theorems/4a5cbf6d-e15d-409d-b98d-8311d3f49b48
-- title:
--   Closed convex function
-- statement:
--   Convex with closed epigraph.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.99

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_Epi

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.99: a closed convex function, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `f` is **closed convex** if `epi f` is a closed convex set. -/
def IsClosedConvexF {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) : Prop :=
  IsConvexF f ∧ IsClosed (Epi f)

end DiscreteConvex.IntegralConvexityB


