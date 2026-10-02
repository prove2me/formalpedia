-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegerInterval
-- name    : DiscreteConvex_IntegralConvexityC_IntegerInterval
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:59.798042+00:00
-- url     : https://prove2.me/theorems/85f07093-bb89-4b9a-9c41-1cfce9754973
-- title:
--   Integer interval
-- statement:
--   $[a,b]=\{x\in\mathbb Z^n:a(i)\le x(i)\le b(i)\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.92, Eq. (3.54).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.92, Eq. (3.54)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.92, Eq. (3.54): the integer interval, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- The integer interval `[a,b] = \{x ∈ Zⁿ : a(i) ≤ x(i) ≤ b(i)\}` (Eq. (3.54)), finite
endpoints. -/
def IntegerInterval {n : ℕ} (a b : Fin n → ℤ) : Set (Fin n → ℤ) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}

end DiscreteConvex.IntegralConvexityC


