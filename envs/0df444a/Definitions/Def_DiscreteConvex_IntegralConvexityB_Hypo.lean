-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityB_Hypo
-- name    : DiscreteConvex_IntegralConvexityB_Hypo
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:57:32.189206+00:00
-- url     : https://prove2.me/theorems/8917376d-6aeb-4602-9fdc-64df273f09a7
-- title:
--   Hypograph of a function
-- statement:
--   $\operatorname{hyp}h=\{(x,Y):Y\le h(x)\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, dual to p.79, Eq. (3.14).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, dual to p.79, Eq. (3.14)

import Mathlib

/-!
The hypograph of a function (dual to Eq. (3.14) for concave functions), in
`DiscreteConvex.IntegralConvexityB`.
-/

namespace DiscreteConvex.IntegralConvexityB

/-- `hyp h = \{(x,Y) ∈ Rⁿ⁺¹ | Y ≤ h(x)\}`, the hypograph of `h`. -/
def Hypo {V : Type*} (h : (V → ℝ) → EReal) : Set ((V → ℝ) × ℝ) :=
  {p | (p.2 : EReal) ≤ h p.1}

end DiscreteConvex.IntegralConvexityB


