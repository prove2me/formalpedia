-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_DemandSet
-- name    : DiscreteConvex_EconomicEquilibriumB_DemandSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:54:49.599289+00:00
-- url     : https://prove2.me/theorems/576c49d8-60a4-4adb-a3c2-1bfc0c1a3dc0
-- title:
--   DemandSet
-- statement:
--   The demand set $D_h(p)=\arg\max(U_h(x)-\langle p,x\rangle)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ArgMaxBot
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShift

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The demand set `Dh(p) = arg max (Uh(x) − ⟨p,x⟩)`. -/
def DemandSet (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) : Set (K → ℤ) := ArgMaxBot (PriceShift U p)

end DiscreteConvex.EconomicEquilibriumB


