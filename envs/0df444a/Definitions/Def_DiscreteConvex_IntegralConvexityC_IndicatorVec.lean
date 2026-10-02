-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_IndicatorVec
-- name    : DiscreteConvex_IntegralConvexityC_IndicatorVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:12.78216+00:00
-- url     : https://prove2.me/theorems/687a7c8f-f844-45c5-8b16-9f64858b8e90
-- title:
--   0/1-indicator vector
-- statement:
--   $\chi_Y$: $1$ on $Y$, $0$ elsewhere.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.94

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.94: the {0,1}-indicator vector `χ_Y`, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `χ_Y ∈ Zⁿ`: `1` on `Y`, `0` elsewhere. -/
def IndicatorVec {n : ℕ} (Y : Finset (Fin n)) : Fin n → ℤ :=
  fun i => if i ∈ Y then 1 else 0

end DiscreteConvex.IntegralConvexityC


