-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_ConvexClosureSet
-- name    : DiscreteConvex_IntegralConvexityB_ConvexClosureSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:02:32.860724+00:00
-- url     : https://prove2.me/theorems/6b71e517-5018-4d35-9658-59b38abda42e
-- title:
--   Convex hull of a discrete integer set
-- statement:
--   $\bar S=\operatorname{conv}(S)$ under the real embedding.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityB_EmbedZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, "convex closure"/"convex hull": the real
convex hull of a discrete set of integer vectors, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- The convex hull `S̄ ⊆ Rⱽ` of a discrete set `S ⊆ Zⱽ`. -/
def ConvexClosureSet {V : Type*} (S : Set (V → ℤ)) : Set (V → ℝ) :=
  convexHull ℝ (EmbedZR '' S)

end DiscreteConvex.IntegralConvexityB


