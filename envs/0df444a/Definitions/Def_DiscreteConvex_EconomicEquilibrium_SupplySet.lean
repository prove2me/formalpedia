-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_SupplySet
-- name    : DiscreteConvex_EconomicEquilibrium_SupplySet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:57:48.568989+00:00
-- url     : https://prove2.me/theorems/d94274cb-9a5c-4cef-8111-578f9364a8d3
-- title:
--   Supply set of a producer (Eq. 11.1)
-- statement:
--   The supply set $S_l(p) = \arg\max_{y \in \mathbb Z^K} (\langle p,y\rangle - C_l(y))$ (Eq. (11.1)) of a producer with cost function $C_l$ at price $p$, restated equivalently as $\arg\min C_l[-p]$ (the book's own notation from p.336 on).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_PriceShiftConvex
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_ArgMinTop

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.324, Eq. (11.1): the supply set of a producer, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The supply set `Sl(p) = arg max_{y ∈ Zᴷ} (⟨p,y⟩ − Cl(y))` (Eq. (11.1)) of a producer with cost
function `Cl` at price `p`, restated equivalently as `arg min Cl[−p]` (the book's own notation
from p.336 on: `yl ∈ arg min Cl[−p]`). -/
def SupplySet {K : Type*} [Fintype K] (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) : Set (K → ℤ) :=
  ArgMinTop (PriceShiftConvex C p)

end DiscreteConvex.EconomicEquilibrium


