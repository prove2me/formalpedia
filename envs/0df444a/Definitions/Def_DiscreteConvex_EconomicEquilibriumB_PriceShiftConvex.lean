-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShiftConvex
-- name    : DiscreteConvex_EconomicEquilibriumB_PriceShiftConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:39.873927+00:00
-- url     : https://prove2.me/theorems/67fdc269-cd25-403d-8edd-481fcf84c487
-- title:
--   PriceShiftConvex
-- statement:
--   The price-shifted cost $C[-p](y)=C(y)-\langle p,y\rangle$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1), redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The price-shifted cost `C[−p](y) = C(y) − ⟨p,y⟩`. -/
def PriceShiftConvex (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) (y : K → ℤ) : WithTop ℝ :=
  C y + ((-(∑ k, p k * (y k : ℝ)) : ℝ) : WithTop ℝ)

end DiscreteConvex.EconomicEquilibriumB


