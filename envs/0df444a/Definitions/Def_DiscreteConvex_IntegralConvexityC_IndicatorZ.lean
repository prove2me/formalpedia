-- Prove2me | Definitions.Def_DiscreteConvex_IntegralConvexityC_IndicatorZ
-- name    : DiscreteConvex_IntegralConvexityC_IndicatorZ
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:09:16.979187+00:00
-- url     : https://prove2.me/theorems/ca4c0933-05de-4eb3-bb1a-83342450e8a5
-- title:
--   Indicator function of a discrete set
-- statement:
--   $\delta_S:\mathbb Z^n\to\{0,+\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.96.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.96

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.96, Eq. (3.51)-style: the indicator function
of a discrete set, in `DiscreteConvex.IntegralConvexityC`.
-/

namespace DiscreteConvex.IntegralConvexityC

open Classical in
/-- `δ_S : Zⁿ → \{0,+∞\}`: `0` on `S`, `+∞` off it. -/
noncomputable def IndicatorZ {n : ℕ} (S : Set (Fin n → ℤ)) : (Fin n → ℤ) → WithTop ℝ :=
  fun x => if x ∈ S then (0 : WithTop ℝ) else ⊤

end DiscreteConvex.IntegralConvexityC


