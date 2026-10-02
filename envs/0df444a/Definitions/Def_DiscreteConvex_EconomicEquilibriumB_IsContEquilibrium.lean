-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsContEquilibrium
-- name    : DiscreteConvex_EconomicEquilibriumB_IsContEquilibrium
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:14:17.345828+00:00
-- url     : https://prove2.me/theorems/917c016c-3056-45e3-a0c5-762526be9e88
-- title:
--   IsContEquilibrium
-- statement:
--   $((x_h),(y_l),p)$ is an equilibrium of the derived continuous economy for $x^\circ$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337-338, redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.337-338, redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ContDemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_ContSupplySet

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `((xh), (yl), p)` is an equilibrium of the derived continuous economy for `x°`. -/
def IsContEquilibrium {H L : Type*} [Fintype H] [Fintype L] (U : H → (K → ℤ) → WithBot ℝ)
    (C : L → (K → ℤ) → WithTop ℝ) (x0 : K → ℤ) (x : H → (K → ℝ)) (y : L → (K → ℝ)) (p : K → ℝ) :
    Prop :=
  (∀ h : H, x h ∈ ContDemandSet (U h) p) ∧ (∀ l : L, y l ∈ ContSupplySet (C l) p) ∧
  (∑ h, x h) = (fun k => (x0 k : ℝ)) + ∑ l, y l ∧ (∀ k : K, 0 ≤ p k)

-- ===== The gross-substitutes-style characterizations (§11.3) =====

end DiscreteConvex.EconomicEquilibriumB


