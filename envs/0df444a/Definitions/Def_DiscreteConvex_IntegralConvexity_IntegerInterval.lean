-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_IntegerInterval
-- name    : DiscreteConvex_IntegralConvexity_IntegerInterval
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:48:49.154614+00:00
-- url     : https://prove2.me/theorems/4eb62dc9-f2b0-4349-8558-1771d380f3c2
-- title:
--   Integer interval [a,b] (Eq. 3.54, finite case)
-- statement:
--   The **integer interval** $[a,b] = \{x \in \mathbb Z^n : a(i) \le x(i) \le b(i),\ i=1,\dots,n\}$ (Eq. (3.54)), specialized to finite endpoints $a, b \in \mathbb Z^n$ (the book also allows entries $\pm\infty$; only the finite case is needed for Proposition 3.19).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.92, Eq. (3.54).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.92, Eq. (3.54)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.92, Eq. (3.54): the integer interval
`[a,b]_Z`, specialized to finite endpoints `a, b ∈ Zⁿ` (the finite case used by Proposition
3.19), in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- The integer interval `[a,b] = \{x ∈ Zⁿ : a(i) ≤ x(i) ≤ b(i)\ (i = 1,…,n)\}` (Eq. (3.54)),
specialized to finite endpoints `a, b : Fin n → ℤ` (the book allows entries `±∞`; only the
finite case is needed for Proposition 3.19). -/
def IntegerInterval {n : ℕ} (a b : Fin n → ℤ) : Set (Fin n → ℤ) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}

end DiscreteConvex.IntegralConvexity


