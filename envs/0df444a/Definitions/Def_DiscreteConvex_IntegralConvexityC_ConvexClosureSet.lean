-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_ConvexClosureSet
-- name    : DiscreteConvex_IntegralConvexityC_ConvexClosureSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:10:21.680134+00:00
-- url     : https://prove2.me/theorems/9ac377d7-dcf7-4fca-9903-f09a31cadcc7
-- title:
--   Convex hull of a discrete integer set
-- statement:
--   $\bar S=\operatorname{conv}(S)$ under the real embedding.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.98

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_EmbedZR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.98, "convex closure": the real convex hull of
a discrete set of integer vectors, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The convex hull `S̄ ⊆ Rⁿ` of a discrete set `S ⊆ Zⁿ`. -/
def ConvexClosureSet {n : ℕ} (S : Set (Fin n → ℤ)) : Set (Fin n → ℝ) :=
  convexHull ℝ (EmbedZR '' S)

end DiscreteConvex.IntegralConvexityC


