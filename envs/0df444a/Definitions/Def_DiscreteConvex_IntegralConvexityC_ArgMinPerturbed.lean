-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_ArgMinPerturbed
-- name    : DiscreteConvex_IntegralConvexityC_ArgMinPerturbed
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:05.669605+00:00
-- url     : https://prove2.me/theorems/21540b2a-2e79-4e1a-98d0-903f2c1b934c
-- title:
--   Minimizer set of a linearly perturbed function
-- statement:
--   $\arg\min f[-p]$, stated additively.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eqs. (3.69)-(3.70).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93, Eqs. (3.69)-(3.70)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93, Eq. (3.69)-(3.70): the minimizer set of a
linearly perturbed function, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `arg min f[-p]`, stated additively to avoid subtraction on `WithTop ℝ`. -/
def ArgMinPerturbed {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) (p : Fin n → ℝ) :
    Set (Fin n → ℤ) :=
  {x | ∀ y : Fin n → ℤ,
    f x + ((∑ i, p i * (y i : ℝ) : ℝ) : WithTop ℝ) ≤ f y + ((∑ i, p i * (x i : ℝ) : ℝ) : WithTop ℝ)}

end DiscreteConvex.IntegralConvexityC


