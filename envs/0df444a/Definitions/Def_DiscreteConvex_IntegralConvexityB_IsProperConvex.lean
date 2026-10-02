-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConvex
-- name    : DiscreteConvex_IntegralConvexityB_IsProperConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:03:49.86581+00:00
-- url     : https://prove2.me/theorems/e1db718a-55eb-47ef-9c78-0a6d1080d2ae
-- title:
--   Proper convex function
-- statement:
--   Convex, never $-\infty$, nonempty effective domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsConvexF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_NeverBot
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.97: a proper convex function, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- A **proper convex function**: convex, never `-∞`, with nonempty effective domain. -/
def IsProperConvex {V : Type*} [Fintype V] (f : (V → ℝ) → EReal) : Prop :=
  IsConvexF f ∧ NeverBot f ∧ (DomE f).Nonempty

end DiscreteConvex.IntegralConvexityB


