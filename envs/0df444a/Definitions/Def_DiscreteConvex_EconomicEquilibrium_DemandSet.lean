-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_DemandSet
-- name    : DiscreteConvex_EconomicEquilibrium_DemandSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:57:51.619999+00:00
-- url     : https://prove2.me/theorems/f90a679b-6968-4d4e-8cef-38fe9947a2b8
-- title:
--   Demand set of a consumer (Eq. 11.8)
-- statement:
--   The demand set $D_h(p) = \arg\max_{x \in \mathbb Z^K} (U_h(x) - \langle p,x\rangle)$ (Eq. (11.8)) of a consumer with utility function $U_h$ at price $p$: the consumption bundles that maximize her utility net of expenditure.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325, Eq. (11.8)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_PriceShift
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_ArgMaxBot

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.325, Eq. (11.8): the demand set of a consumer, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The demand set `Dh(p) = arg max_{x ∈ Zᴷ} (Uh(x) − ⟨p,x⟩)` (Eq. (11.8)) of a consumer with
utility function `Uh` at price `p`. -/
def DemandSet {K : Type*} [Fintype K] (U : (K → ℤ) → WithBot ℝ) (p : K → ℝ) : Set (K → ℤ) :=
  ArgMaxBot (PriceShift U p)

end DiscreteConvex.EconomicEquilibrium


