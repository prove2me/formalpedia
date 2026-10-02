-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_IntPts
-- name    : DiscreteConvex_MConvexSetsB_IntPts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:26:29.041297+00:00
-- url     : https://prove2.me/theorems/a2a255d0-7e0a-48fa-a7d3-735b8f9c2770
-- title:
--   IntPts
-- statement:
--   The integer points of $\mathbb R^V$: $\{x : \forall v,\exists k \in \mathbb Z,\ x(v)=k\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.107-116 (supporting several results).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.107-116 (supporting several results)

import Mathlib

/-!
The integer points `Zⱽ` viewed as a subset of `Rⱽ`, used throughout this mission (Murota,
*Discrete Convex Analysis*, SIAM 2003, pp.107-116), in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- The integer points of `Rⱽ`: `\{x : ∀v, ∃k:ℤ, x(v)=k\}`. -/
def IntPts {V : Type*} : Set (V → ℝ) :=
  {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)}

end DiscreteConvex.MConvexSetsB


