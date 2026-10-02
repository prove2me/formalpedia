-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexity_IndicatorVec
-- name    : DiscreteConvex_IntegralConvexity_IndicatorVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:48:32.132691+00:00
-- url     : https://prove2.me/theorems/a4e8f87c-eb11-4546-997d-ad6829dea8d0
-- title:
--   Indicator vector of a coordinate set
-- statement:
--   The **indicator vector** $\chi_Y \in \mathbb Z^n$ of a subset $Y$ of the coordinate index set $\{1,\dots,n\}$ has $\chi_Y(i) = 1$ for $i \in Y$ and $\chi_Y(i) = 0$ otherwise. Used in Theorem 3.21's local-exchange form $x + \chi_Y - \chi_Z$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.94: the $\{0,1\}$-indicator vector `χ_Y` of a
subset `Y` of the coordinate index set, used in Theorem 3.21's local-exchange form
`x + χ_Y - χ_Z`, in `DiscreteConvex.IntegralConvexity`.
-/

namespace DiscreteConvex.IntegralConvexity

/-- The indicator vector `χ_Y ∈ Zⁿ` of a set `Y` of coordinates: `1` on `Y`, `0` elsewhere. -/
def IndicatorVec {n : ℕ} (Y : Finset (Fin n)) : Fin n → ℤ :=
  fun i => if i ∈ Y then 1 else 0

end DiscreteConvex.IntegralConvexity


