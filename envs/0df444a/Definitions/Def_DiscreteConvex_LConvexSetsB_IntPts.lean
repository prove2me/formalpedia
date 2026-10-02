-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSetsB_IntPts
-- name    : DiscreteConvex_LConvexSetsB_IntPts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:41:55.994063+00:00
-- url     : https://prove2.me/theorems/195ea8c0-6a8e-4fe8-bc64-c56f86eb6a7b
-- title:
--   IntPts
-- statement:
--   The integer points of $\mathbb R^V$: $\{x : \forall v,\exists k \in \mathbb Z,\ x(v)=k\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.122-128 (supporting several results).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.122-128 (supporting several results)

import Mathlib

/-!
The integer points `Zⱽ` viewed as a subset of `Rⱽ`, used throughout this mission (Murota,
*Discrete Convex Analysis*, SIAM 2003, pp.122-128), in `DiscreteConvex.LConvexSetsB`.
-/

namespace DiscreteConvex.LConvexSetsB

/-- The integer points of `Rⱽ`: `\{x : ∀v, ∃k:ℤ, x(v)=k\}`. -/
def IntPts {V : Type*} : Set (V → ℝ) :=
  {x : V → ℝ | ∀ v, ∃ k : ℤ, x v = (k : ℝ)}

end DiscreteConvex.LConvexSetsB


