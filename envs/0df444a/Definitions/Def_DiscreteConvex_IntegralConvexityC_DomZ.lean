-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_DomZ
-- name    : DiscreteConvex_IntegralConvexityC_DomZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:51.432701+00:00
-- url     : https://prove2.me/theorems/3133b256-226b-4482-949c-0f457cb6d1e7
-- title:
--   Effective domain (integer lattice)
-- statement:
--   $\operatorname{dom}_{\mathbb Z}f=\{x\in\mathbb Z^n:f(x)\ne+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.93

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.93: the effective domain `dom_Z f`, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `dom_Z f = \{x ∈ Zⁿ : f(x) ≠ +∞\}`. -/
def DomZ {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Set (Fin n → ℤ) :=
  {x | f x ≠ ⊤}

end DiscreteConvex.IntegralConvexityC


