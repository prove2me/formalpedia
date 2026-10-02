-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityD_IndicatorWT
-- name    : DiscreteConvex_ConjugacyDualityD_IndicatorWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:56:19.875497+00:00
-- url     : https://prove2.me/theorems/e2fb9fb8-15f0-46a3-b27c-875db403677b
-- title:
--   IndicatorWT
-- statement:
--   The $\{0,+\infty\}$-valued indicator function $\delta_B$ of a set $B$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.59)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.235, Eq. (8.59)-adjacent

import Mathlib

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The `{0,+∞}`-valued indicator function of a set. -/
noncomputable def IndicatorWT (B : Set (V → ℤ)) (z : V → ℤ) : WithTop ℝ := if z ∈ B then 0 else ⊤

end DiscreteConvex.ConjugacyDualityD


