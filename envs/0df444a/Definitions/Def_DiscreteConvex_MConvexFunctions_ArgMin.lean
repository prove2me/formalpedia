-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
-- name    : DiscreteConvex_MConvexFunctions_ArgMin
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:51:55.249836+00:00
-- url     : https://prove2.me/theorems/4e8b11fd-bb58-47d1-8846-021d64fa8de0
-- title:
--   Minimizer set on the integer lattice
-- statement:
--   The minimizer set $\arg\min f = \{x \in \mathbb Z^V : f(x) \le f(y)\ \forall y \in \mathbb Z^V\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.148-149.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.148-149

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.148-149: the minimizer set of a function on
the integer lattice, in `DiscreteConvex.MConvexFunctions`.
-/

namespace DiscreteConvex.MConvexFunctions

/-- The minimizer set `arg min f = \{x ∈ Zⱽ : f(x) ≤ f(y)\ ∀y ∈ Zⱽ\}`. -/
def ArgMin {V : Type*} (f : (V → ℤ) → WithTop ℝ) : Set (V → ℤ) :=
  {x | ∀ y, f x ≤ f y}

end DiscreteConvex.MConvexFunctions


