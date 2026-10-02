-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSets_ConvexClosureSet
-- name    : DiscreteConvex_LConvexSets_ConvexClosureSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:35:07.072993+00:00
-- url     : https://prove2.me/theorems/bbacff73-5d4d-4e84-957d-b6b41aaacc2a
-- title:
--   Real convex hull of a discrete integer set
-- statement:
--   The convex hull $\bar D \subseteq \mathbb R^V$ of a discrete set $D \subseteq \mathbb Z^V$, i.e. $\operatorname{conv}(D)$ under the real embedding of $\mathbb Z^V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.123, 125, used in Theorems 5.2 and 5.7.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.123, 125 (supporting Theorems 5.2, 5.7)

import Mathlib

/-!
The real convex hull of a discrete set of integer vectors, used for the hole-free property
(Theorem 5.2) and the intersection properties (Theorem 5.7) of L-convex sets (Murota, *Discrete
Convex Analysis*, SIAM 2003, pp.123, 125), in `DiscreteConvex.LConvexSets`.
-/

namespace DiscreteConvex.LConvexSets

/-- The convex hull `D̄ ⊆ Rⱽ` of a discrete set `D ⊆ Zⱽ`, i.e. `conv(D)` under the real
embedding of `Zⱽ`. -/
def ConvexClosureSet {V : Type*} (D : Set (V → ℤ)) : Set (V → ℝ) :=
  convexHull ℝ ((fun p : V → ℤ => (fun v => (p v : ℝ))) '' D)

end DiscreteConvex.LConvexSets


