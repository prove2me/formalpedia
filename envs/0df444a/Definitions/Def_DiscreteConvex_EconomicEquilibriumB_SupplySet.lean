-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SupplySet
-- name    : DiscreteConvex_EconomicEquilibriumB_SupplySet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:55:23.353709+00:00
-- url     : https://prove2.me/theorems/8cf6ed93-c0d0-4033-bd07-df8b7184ee93
-- title:
--   SupplySet
-- statement:
--   The supply set $S_l(p)=\arg\min C_l[-p]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ArgMinTop
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShiftConvex

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The supply set `Sl(p) = arg min Cl[−p]`. -/
def SupplySet (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) : Set (K → ℤ) :=
  ArgMinTop (PriceShiftConvex C p)

end DiscreteConvex.EconomicEquilibriumB


