-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_IsEquilibrium
-- name    : DiscreteConvex_EconomicEquilibriumB_IsEquilibrium
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:04:51.05548+00:00
-- url     : https://prove2.me/theorems/4678e163-fd22-4618-a6da-554a229160e0
-- title:
--   IsEquilibrium
-- statement:
--   $((x_h),(y_l),p)$ is an equilibrium for total initial endowment $x^\circ$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325-326, Eqs. (11.9)-(11.12), redeclared.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.325-326, Eqs. (11.9)-(11.12), redeclared

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SupplySet

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
open scoped Pointwise
variable {K : Type*} [Fintype K] [DecidableEq K]
/-- `((xh), (yl), p)` is an equilibrium for total initial endowment `x°`. -/
def IsEquilibrium {H L : Type*} [Fintype H] [Fintype L] (U : H → (K → ℤ) → WithBot ℝ)
    (C : L → (K → ℤ) → WithTop ℝ) (x0 : K → ℤ) (x : H → (K → ℤ)) (y : L → (K → ℤ)) (p : K → ℝ) :
    Prop :=
  (∀ h : H, x h ∈ DemandSet (U h) p) ∧ (∀ l : L, y l ∈ SupplySet (C l) p) ∧
  (∑ h, x h) = x0 + ∑ l, y l ∧ (∀ k : K, 0 ≤ p k)

end DiscreteConvex.EconomicEquilibriumB


