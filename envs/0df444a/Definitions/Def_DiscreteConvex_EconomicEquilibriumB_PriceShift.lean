-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShift
-- name    : DiscreteConvex_EconomicEquilibriumB_PriceShift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:43:38.676198+00:00
-- url     : https://prove2.me/theorems/3820fcfe-5ec9-4add-a55d-9da0fefb3020
-- title:
--   PriceShift
-- statement:
--   The price-shifted utility $U[-p](x)=U(x)-\langle p,x\rangle$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8), redeclared

import Mathlib

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The price-shifted utility `U[−p](x) = U(x) − ⟨p,x⟩`. -/
def PriceShift (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (x : K → ℤ) : WithBot ℝ :=
  U x + ((-(∑ k, p k * (x k : ℝ)) : ℝ) : WithBot ℝ)

end DiscreteConvex.EconomicEquilibriumB


