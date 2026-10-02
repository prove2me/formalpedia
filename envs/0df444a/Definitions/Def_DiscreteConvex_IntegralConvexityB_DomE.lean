-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_DomE
-- name    : DiscreteConvex_IntegralConvexityB_DomE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:58:36.84056+00:00
-- url     : https://prove2.me/theorems/48d4d1fe-a41b-4fbb-a698-9a38f44e3763
-- title:
--   Effective domain
-- statement:
--   $\operatorname{dom}f=\{x:-\infty<f(x)<+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.3).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.3)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.97, Eq. (3.3): the effective domain of a
function, in `DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `dom f = \{x | -∞ < f(x) < +∞\}` (Eq. (3.3)). -/
def DomE {V : Type*} (f : (V → ℝ) → EReal) : Set (V → ℝ) :=
  {x | f x ≠ ⊤ ∧ f x ≠ ⊥}

end DiscreteConvex.IntegralConvexityB


