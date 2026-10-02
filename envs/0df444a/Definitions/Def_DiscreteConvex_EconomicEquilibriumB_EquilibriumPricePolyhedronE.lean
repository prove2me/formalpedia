-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPricePolyhedronE
-- name    : DiscreteConvex_EconomicEquilibriumB_EquilibriumPricePolyhedronE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:05:07.967102+00:00
-- url     : https://prove2.me/theorems/32291f2f-18e4-4c1d-ad95-102c68097a06
-- title:
--   The price inequality system in the extended reals
-- statement:
--   The inequality system (11.43) with its bounds read in $\overline{\mathbb{R}}$: $\max(0,\ell(j))\le p(j)\le u(j)$ for every good $j$, and $p(j)-p(i)\le u(i,j)$ for $i\ne j$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §11.5, Eq. (11.43).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §11.5, Eq. (11.43)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_LBoundJE
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundJE
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundIJE

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The inequality system (11.43) with its bounds read in `EReal`, so that the book's `-∞` and
`+∞` cases stay infinite instead of collapsing to `0`. -/
def EquilibriumPricePolyhedronE {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) : Set (K → ℝ) :=
  {p | (∀ j : K, max 0 (LBoundJE U C x y j) ≤ ((p j : ℝ) : EReal) ∧
        ((p j : ℝ) : EReal) ≤ UBoundJE U C x y j) ∧
    ∀ i j : K, i ≠ j → ((p j - p i : ℝ) : EReal) ≤ UBoundIJE U C x y i j}

end DiscreteConvex.EconomicEquilibriumB


