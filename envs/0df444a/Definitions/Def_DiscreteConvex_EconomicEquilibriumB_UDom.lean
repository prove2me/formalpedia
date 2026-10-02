-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UDom
-- name    : DiscreteConvex_EconomicEquilibriumB_UDom
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:47.803713+00:00
-- url     : https://prove2.me/theorems/de0f90fd-1a61-46e8-a0f8-2d99d10dda3f
-- title:
--   UDom
-- statement:
--   The effective domain $\operatorname{dom}U=\{x\in\mathbb Z^K:U(x)\ne-\infty\}$ of a utility-type function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The effective domain `dom U = {x ∈ Zᴷ : U(x) ≠ −∞}` of a utility-type function. -/
def UDom (U : (K → ℤ) → WithBot ℝ) : Set (K → ℤ) := {x | U x ≠ ⊥}

end DiscreteConvex.EconomicEquilibriumB


