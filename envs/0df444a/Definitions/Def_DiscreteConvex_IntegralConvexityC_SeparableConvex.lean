-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_SeparableConvex
-- name    : DiscreteConvex_IntegralConvexityC_SeparableConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:10:22.09209+00:00
-- url     : https://prove2.me/theorems/e8cf9b42-5acc-4c74-b0a0-648f7e242c8a
-- title:
--   Separable convex function
-- statement:
--   $f(x)=\sum_i f_i(x(i))$ with $f_i\in C[\mathbb Z\to\mathbb R]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.95, Eq. (3.67).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.95, Eq. (3.67)

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_UnivDiscreteConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.95, Eq. (3.67): a separable convex function,
in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `f` is a **separable convex function** (Eq. (3.67)): `f(x) = ∑ᵢ fᵢ(x(i))` with each
`fᵢ ∈ C[Z→R]`. -/
def SeparableConvex {n : ℕ} (f : (Fin n → ℤ) → WithTop ℝ) : Prop :=
  ∃ fi : Fin n → ℤ → WithTop ℝ, (∀ i, UnivDiscreteConvex (fi i)) ∧
    ∀ x : Fin n → ℤ, f x = ∑ i, fi i (x i)

end DiscreteConvex.IntegralConvexityC


