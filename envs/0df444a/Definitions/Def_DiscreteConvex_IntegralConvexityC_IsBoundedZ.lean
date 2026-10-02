-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_IsBoundedZ
-- name    : DiscreteConvex_IntegralConvexityC_IsBoundedZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:10:29.717019+00:00
-- url     : https://prove2.me/theorems/ea90d033-831c-4457-99b2-c2bdbc3a6439
-- title:
--   Boundedness of a discrete set
-- statement:
--   $S$ contained in some finite integer interval.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegerInterval

/-!
Boundedness of a discrete set, used in Theorem 3.29's "nonempty bounded effective domain"
hypothesis (Murota, *Discrete Convex Analysis*, SIAM 2003, p.97), in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `S` is **bounded**: contained in some finite integer interval. -/
def IsBoundedZ {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  ∃ lo hi : Fin n → ℤ, S ⊆ IntegerInterval lo hi

end DiscreteConvex.IntegralConvexityC


