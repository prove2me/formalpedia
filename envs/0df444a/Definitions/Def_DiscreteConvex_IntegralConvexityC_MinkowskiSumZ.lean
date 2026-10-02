-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_MinkowskiSumZ
-- name    : DiscreteConvex_IntegralConvexityC_MinkowskiSumZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:15.58383+00:00
-- url     : https://prove2.me/theorems/d4b31ea1-d018-4040-af18-653b99771995
-- title:
--   Discrete Minkowski sum
-- statement:
--   $S_1+S_2=\{x_1+x_2:x_1\in S_1,x_2\in S_2\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, Eq. (3.52).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.90, Eq. (3.52)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.90, Eq. (3.52): the discrete Minkowski sum, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `S1 + S2 = \{x1+x2 | x1 ∈ S1, x2 ∈ S2\}` (Eq. (3.52)). -/
def MinkowskiSumZ {n : ℕ} (S1 S2 : Set (Fin n → ℤ)) : Set (Fin n → ℤ) :=
  {x | ∃ x1 ∈ S1, ∃ x2 ∈ S2, x = x1 + x2}

end DiscreteConvex.IntegralConvexityC


