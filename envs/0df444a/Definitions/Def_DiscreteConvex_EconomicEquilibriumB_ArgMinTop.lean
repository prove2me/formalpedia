-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ArgMinTop
-- name    : DiscreteConvex_EconomicEquilibriumB_ArgMinTop
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:37.38043+00:00
-- url     : https://prove2.me/theorems/b87de828-1f1b-4276-bde2-56fba93a30b2
-- title:
--   ArgMinTop
-- statement:
--   The minimizer set of a $\mathbb R\cup\{+\infty\}$-valued function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The minimizer set of a `WithTop ℝ`-valued function. -/
def ArgMinTop (g : (K → ℤ) → WithTop ℝ) : Set (K → ℤ) := {x | ∀ y, g x ≤ g y}

end DiscreteConvex.EconomicEquilibriumB


