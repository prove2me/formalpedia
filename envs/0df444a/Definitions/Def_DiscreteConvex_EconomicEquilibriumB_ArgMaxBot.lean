-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ArgMaxBot
-- name    : DiscreteConvex_EconomicEquilibriumB_ArgMaxBot
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:34.438916+00:00
-- url     : https://prove2.me/theorems/3be8999c-3165-4716-9a6d-ad51fd40fb79
-- title:
--   ArgMaxBot
-- statement:
--   The maximizer set of a $\mathbb R\cup\{-\infty\}$-valued function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The maximizer set of a `WithBot ℝ`-valued function. -/
def ArgMaxBot (g : (K → ℤ) → WithBot ℝ) : Set (K → ℤ) := {x | ∀ y, g y ≤ g x}

end DiscreteConvex.EconomicEquilibriumB


