-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPricePolyhedron
-- name    : DiscreteConvex_EconomicEquilibriumB_EquilibriumPricePolyhedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:56:46.700547+00:00
-- url     : https://prove2.me/theorems/4ccee5eb-1d50-41c4-9870-ca723382c49b
-- title:
--   EquilibriumPricePolyhedron
-- statement:
--   The explicit inequality-system description of $P^*(x^\circ)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Eq. (11.43).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.343, Eq. (11.43)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_LBoundJ
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundJ
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_UBoundIJ

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The explicit inequality-system description of `P*(x°)`, Eq. (11.43). -/
def EquilibriumPricePolyhedron {H L : Type*} [Fintype H] [Fintype L] [Nonempty H] [Nonempty L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ))
    (y : L → (K → ℤ)) : Set (K → ℝ) :=
  {p | (∀ j : K, max 0 (LBoundJ U C x y j) ≤ p j ∧ p j ≤ UBoundJ U C x y j) ∧
    ∀ i j : K, i ≠ j → p j - p i ≤ UBoundIJ U C x y i j}

-- ===== Theorems =====

end DiscreteConvex.EconomicEquilibriumB


