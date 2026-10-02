-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShiftGen
-- name    : DiscreteConvex_EconomicEquilibriumB_PriceShiftGen
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:56:25.113986+00:00
-- url     : https://prove2.me/theorems/28554eeb-0bcd-48d6-87f2-16a734cd5795
-- title:
--   PriceShiftGen
-- statement:
--   $U[-p+p_0\mathbf 1](x)=U(x)-\langle p,x\rangle+p_0\cdot x(K)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, preceding Eq. (11.19).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, preceding Eq. (11.19)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShift

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `U[−p+p0·1](x) = U(x) − ⟨p,x⟩ + p0·x(K)`. -/
def PriceShiftGen (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) (p0 : ℝ) (x : K → ℤ) : WithBot ℝ :=
  PriceShift U p x + ((p0 * (∑ k, (x k : ℝ)) : ℝ) : WithBot ℝ)

end DiscreteConvex.EconomicEquilibriumB


