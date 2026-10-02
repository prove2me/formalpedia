-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_NegGS
-- name    : DiscreteConvex_EconomicEquilibriumB_NegGS
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:04:44.016262+00:00
-- url     : https://prove2.me/theorems/6a84f36b-7dc4-464f-9531-661c4cd65840
-- title:
--   NegGS
-- statement:
--   Axiom (−M$^\natural$-GS[Z]), a version of the gross substitutes property.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, axiom (−M$^\\natural$-GS[Z]).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.330, axiom (−M$^\\natural$-GS[Z])

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ArgMaxBot
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_PriceShiftGen

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- Axiom (−M♮-GS[Z]) (a version of the gross substitutes property). -/
def NegGS (U : (K → ℤ) → WithBot ℝ) : Prop :=
  ∀ p q : K → ℝ, ∀ p0 q0 : ℝ, (∀ k, p k ≤ q k) → p0 ≤ q0 →
    ∀ x : K → ℤ, x ∈ ArgMaxBot (PriceShiftGen U p p0) →
    (ArgMaxBot (PriceShiftGen U q q0)).Nonempty →
    ∃ y : K → ℤ, y ∈ ArgMaxBot (PriceShiftGen U q q0) ∧
      (∀ i : K, p i = q i → x i ≤ y i) ∧ (p0 = q0 → (∑ k, y k) ≤ ∑ k, x k)

end DiscreteConvex.EconomicEquilibriumB


