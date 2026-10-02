-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsE_IndicatorR
-- name    : DiscreteConvex_MConvexFunctionsE_IndicatorR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T00:04:13.791007+00:00
-- url     : https://prove2.me/theorems/c5bdbbeb-96be-40dc-af5c-569fc3b4eda2
-- title:
--   IndicatorR
-- statement:
--   The $\{0,+\infty\}$-valued indicator function of a set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, indicator-function device.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.170, indicator-function device

import Mathlib

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `{0,+∞}`-valued indicator function of a set. -/
noncomputable def IndicatorR (P : Set (V → ℝ)) : (V → ℝ) → WithTop ℝ :=
  fun x => if x ∈ P then (0 : WithTop ℝ) else ⊤

end DiscreteConvex.MConvexFunctionsE


