-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_Epi
-- name    : DiscreteConvex_IntegralConvexityB_Epi
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:57:29.966995+00:00
-- url     : https://prove2.me/theorems/1dcc5e8a-5890-4d37-864d-1a031ea6ba2d
-- title:
--   Epigraph of a function
-- statement:
--   $\operatorname{epi}f=\{(x,Y):Y\ge f(x)\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, Eq. (3.14).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.79, Eq. (3.14)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.79, Eq. (3.14): the epigraph of a function, in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `epi f = \{(x,Y) ∈ Rⁿ⁺¹ | Y ≥ f(x)\}` (Eq. (3.14)). -/
def Epi {V : Type*} (f : (V → ℝ) → EReal) : Set ((V → ℝ) × ℝ) :=
  {p | (p.2 : EReal) ≥ f p.1}

end DiscreteConvex.IntegralConvexityB


