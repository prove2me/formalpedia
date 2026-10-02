-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_PrimalFeas
-- name    : DiscreteConvex_IntegralConvexityB_PrimalFeas
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:59:28.521945+00:00
-- url     : https://prove2.me/theorems/1f84fd15-e254-4272-afd8-69099faf31e2
-- title:
--   Primal LP feasible region
-- statement:
--   $P=\{x:Ax=b,x\ge0\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Eq. (3.45).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.107, Eq. (3.45)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.107, Eq. (3.45): the primal LP feasible
region, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `P = \{x ∈ Rⁿ | Ax = b, x ≥ 0\}` (Eq. (3.45)). -/
def PrimalFeas {V W : Type*} [Fintype V] (A : Matrix W V ℝ) (b : W → ℝ) : Set (V → ℝ) :=
  {x | A.mulVec x = b ∧ ∀ j, 0 ≤ x j}

end DiscreteConvex.IntegralConvexityB


