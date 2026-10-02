-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_IsProperConcave
-- name    : DiscreteConvex_IntegralConvexityB_IsProperConcave
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:03:48.790985+00:00
-- url     : https://prove2.me/theorems/f309029e-6151-43d6-865e-e9c8a93377aa
-- title:
--   Proper concave function
-- statement:
--   Concave, never $+\infty$, nonempty effective domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_IsConcaveF
import Definitions.Def_DiscreteConvex_IntegralConvexityB_NeverTop
import Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98: a proper concave function, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- A **proper concave function**: concave, never `+∞`, with nonempty effective domain. -/
def IsProperConcave {V : Type*} [Fintype V] (h : (V → ℝ) → EReal) : Prop :=
  IsConcaveF h ∧ NeverTop h ∧ (DomE h).Nonempty

end DiscreteConvex.IntegralConvexityB


