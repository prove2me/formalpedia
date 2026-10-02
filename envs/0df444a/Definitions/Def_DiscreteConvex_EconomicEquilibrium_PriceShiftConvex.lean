-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_PriceShiftConvex
-- name    : DiscreteConvex_EconomicEquilibrium_PriceShiftConvex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:49:25.583135+00:00
-- url     : https://prove2.me/theorems/45d08340-52c9-4512-9ab0-e46752270554
-- title:
--   Price-shifted cost $C[-p]$
-- statement:
--   The price-shifted cost $C[-p](y) = C(y) - \langle p,y\rangle$ for a cost-type function $C : \mathbb Z^K \to \mathbb R \cup \{+\infty\}$ and a price vector $p \in \mathbb R^K$ (Eq. (11.1), restated via the $C_l[-p]$ notation the book itself uses from p.336 on, e.g. "$y_l \in \arg\min C_l[-p]$").
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.324, Eq. (11.1)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.324, Eq. (11.1), and the notation `Cl[−p]` used
from p.336 on: the price-shifted cost, in `DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- The price-shifted cost `C[−p](y) = C(y) − ⟨p,y⟩` for a cost-type function
`C : Zᴷ → R ∪ {+∞}` and a price vector `p ∈ Rᴷ`. -/
def PriceShiftConvex {K : Type*} [Fintype K] (C : (K → ℤ) → WithTop ℝ) (p : K → ℝ) (y : K → ℤ) :
    WithTop ℝ :=
  C y + ((-(∑ k, p k * (y k : ℝ)) : ℝ) : WithTop ℝ)

end DiscreteConvex.EconomicEquilibrium


