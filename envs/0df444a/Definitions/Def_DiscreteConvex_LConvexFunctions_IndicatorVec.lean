-- Prove2me | Definitions.Def_DiscreteConvex_LConvexFunctions_IndicatorVec
-- name    : DiscreteConvex_LConvexFunctions_IndicatorVec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:13:22.400233+00:00
-- url     : https://prove2.me/theorems/aaecec8a-52cf-43b7-ae3a-ba349ae6ff6e
-- title:
--   Indicator vector of a coordinate set
-- statement:
--   The indicator vector $\chi_Y \in \mathbb Z^V$ of $Y \subseteq V$: $1$ on $Y$, $0$ elsewhere.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.185

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.185: the indicator vector of a subset of the
ground set, in `DiscreteConvex.LConvexFunctions`.
-/

namespace DiscreteConvex.LConvexFunctions

/-- The indicator vector `χ_Y ∈ Zⱽ` of `Y ⊆ V`: `1` on `Y`, `0` elsewhere. -/
def IndicatorVec {V : Type*} [DecidableEq V] (Y : Finset V) : V → ℤ :=
  fun v => if v ∈ Y then 1 else 0

end DiscreteConvex.LConvexFunctions


