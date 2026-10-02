-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
-- name    : DiscreteConvex_IntegralConvexityC_IntegrallyConvexSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:12:24.505193+00:00
-- url     : https://prove2.me/theorems/aee605b0-6c97-49b1-bf5f-7cdf28538d27
-- title:
--   Integrally convex set
-- statement:
--   $S$ with $\delta_S$ integrally convex.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.96.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.96

import Mathlib
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IndicatorZ
import Definitions.Def_DiscreteConvex_IntegralConvexityC_IntegrallyConvex

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.96: an integrally convex set, in
`DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

/-- `S ⊆ Zⁿ` is **integrally convex** if its indicator function `δ_S` is an integrally convex
function. -/
noncomputable def IntegrallyConvexSet {n : ℕ} (S : Set (Fin n → ℤ)) : Prop :=
  IntegrallyConvex (IndicatorZ S)

end DiscreteConvex.IntegralConvexityC


