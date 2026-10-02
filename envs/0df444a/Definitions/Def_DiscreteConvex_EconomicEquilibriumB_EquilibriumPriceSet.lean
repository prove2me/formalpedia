-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_EquilibriumPriceSet
-- name    : DiscreteConvex_EconomicEquilibriumB_EquilibriumPriceSet
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:05:13.881532+00:00
-- url     : https://prove2.me/theorems/914482eb-d610-481c-94f1-adb586923bcf
-- title:
--   EquilibriumPriceSet
-- statement:
--   The set of all equilibrium price vectors for the given allocation $(x,y)$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.342, Eq. (11.23).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.342, Eq. (11.23)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SupplySet

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- The set of all equilibrium price vectors for the given allocation `(x,y)`, Eq. (11.23). -/
def EquilibriumPriceSet {H L : Type*} [Fintype H] [Fintype L] (U : H → (K → ℤ) → WithBot ℝ)
    (C : L → (K → ℤ) → WithTop ℝ) (x : H → (K → ℤ)) (y : L → (K → ℤ)) : Set (K → ℝ) :=
  {p | (∀ h : H, x h ∈ DemandSet (U h) p) ∧ (∀ l : L, y l ∈ SupplySet (C l) p) ∧ ∀ k, 0 ≤ p k}

end DiscreteConvex.EconomicEquilibriumB


