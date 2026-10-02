-- Prove2me | Definitions.Def_DiscreteConvex_LConvexSets_IsIntegerValuedDist
-- name    : DiscreteConvex_LConvexSets_IsIntegerValuedDist
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:35:25.934286+00:00
-- url     : https://prove2.me/theorems/228a2ca8-9b2a-44be-8054-7fef2559b429
-- title:
--   Integer-valuedness of a distance function
-- statement:
--   A distance function $\gamma$ is **integer valued** (the book's $\gamma \in T[\mathbb Z]$, as opposed to $T[\mathbb R]$) if every finite value it takes is an integer. Supporting notion for Theorem 5.5.
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.122, 125 (supporting Theorem 5.5)

import Mathlib

/-!
Integer-valuedness of a distance function, used for the class `T[Z]` in Theorem 5.5 (Murota,
*Discrete Convex Analysis*, SIAM 2003, p.122, p.125), in `DiscreteConvex.LConvexSets`.
-/

namespace DiscreteConvex.LConvexSets

/-- A distance function `γ : V × V → R ∪ {+∞}` is **integer valued** (the book's `γ ∈ T[Z]`,
as opposed to `T[R]`) if every finite value it takes is (the cast of) an integer. -/
def IsIntegerValuedDist {V : Type*} (γ : V → V → WithTop ℝ) : Prop :=
  ∀ u v : V, γ u v = ⊤ ∨ ∃ k : ℤ, γ u v = ((k : ℝ) : WithTop ℝ)

end DiscreteConvex.LConvexSets


