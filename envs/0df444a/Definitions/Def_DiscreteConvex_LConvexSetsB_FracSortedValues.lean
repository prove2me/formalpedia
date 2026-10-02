-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_FracSortedValues
-- name    : DiscreteConvex_LConvexSetsB_FracSortedValues
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:45:37.238788+00:00
-- url     : https://prove2.me/theorems/60379121-b8ea-402e-8edb-d01bcaadb886
-- title:
--   FracSortedValues
-- statement:
--   The distinct nonzero values of the fractional part of $p$, sorted in decreasing order: $\alpha_1 > \alpha_2 > \cdots > \alpha_m$ (preceding Eq. (5.11)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127, preceding Eq. (5.11).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.127, preceding Eq. (5.11)

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.127, preceding Eq. (5.11): the sorted
distinct nonzero values of a fractional part, in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

open Classical in
/-- The distinct nonzero values of the fractional part of `p`, sorted in decreasing order:
`α₁ > α₂ > ⋯ > αₘ` (preceding Eq. (5.11)). -/
noncomputable def FracSortedValues {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) : List ℝ :=
  ((Finset.univ.image (FracVec p)).filter (· ≠ 0)).sort (· ≥ ·)

end DiscreteConvex.LConvexSetsB


