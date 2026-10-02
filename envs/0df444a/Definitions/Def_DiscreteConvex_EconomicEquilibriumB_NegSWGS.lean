-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_NegSWGS
-- name    : DiscreteConvex_EconomicEquilibriumB_NegSWGS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:56:19.386056+00:00
-- url     : https://prove2.me/theorems/f64677f2-f642-40d0-93fb-568b7bd8bbb8
-- title:
--   NegSWGS
-- statement:
--   Axiom (−M$^\natural$-SWGS[Z]), the stepwise gross substitutes property.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, axiom (−M$^\\natural$-SWGS[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.331, axiom (−M$^\\natural$-SWGS[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ArgMaxBot
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShift

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Axiom (−M♮-SWGS[Z]) (the stepwise gross substitutes property). -/
def NegSWGS (U : (K → ℤ) → WithBot ℝ) : Prop :=
  ∀ p : K → ℝ, ∀ x : K → ℤ, x ∈ ArgMaxBot (PriceShift U p) → ∀ i : K,
    (∀ alpha : ℝ, 0 ≤ alpha →
      x ∈ ArgMaxBot (PriceShift U (fun k => p k + (if k = i then alpha else 0)))) ∨
    (∃ alpha : ℝ, 0 ≤ alpha ∧ ∃ y : K → ℤ,
      y ∈ ArgMaxBot (PriceShift U (fun k => p k + (if k = i then alpha else 0))) ∧
      y i = x i - 1 ∧ ∀ j : K, j ≠ i → x j ≤ y j)

-- ===== Structure of the equilibrium price set (§11.5) =====

end DiscreteConvex.EconomicEquilibriumB


