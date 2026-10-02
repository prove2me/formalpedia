-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsContEquilibrium
-- name    : DiscreteConvex_EconomicEquilibrium_IsContEquilibrium
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:07:56.389544+00:00
-- url     : https://prove2.me/theorems/a59aeadc-b9f7-4925-af62-4a5d1997aebf
-- title:
--   Equilibrium of the derived continuous economy
-- statement:
--   $((x_h \mid h \in H), (y_l \mid l \in L), p)$ is an equilibrium of the **derived continuous economy** for total initial endowment $x^\circ \in \mathbb Z^K$ (Eqs. (11.33), (11.34), (11.14), (11.12)): every consumer's continuous allocation $x_h$ lies in her continuous demand set $\hat D_h(p)$ (11.33), every producer's continuous allocation $y_l$ lies in his continuous supply set $\hat S_l(p)$ (11.34), the supply-demand balance $\sum_h x_h = x^\circ + \sum_l y_l$ holds (11.14), and the price vector $p$ is nonnegative (11.12). The continuous-model analogue of `IsEquilibrium`, used as the hypothesis of Theorem 11.14.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.337-338, Eqs. (11.33), (11.34), (11.14), (11.12).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.337-338, Eqs. (11.33), (11.34), (11.14), (11.12)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_ContDemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_ContSupplySet

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, pp.337-338, Eqs. (11.33), (11.34), (11.14),
(11.12): an equilibrium of the derived continuous economy, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- `((xh | h ∈ H), (yl | l ∈ L), p)` is an equilibrium of the **derived continuous economy** for
total initial endowment `x° ∈ Zᴷ` (Eqs. (11.33), (11.34), (11.14), (11.12)): every consumer's
continuous allocation `x h` lies in her continuous demand set `D̂h(p)` (11.33), every producer's
continuous allocation `y l` lies in his continuous supply set `Ŝl(p)` (11.34), the supply-demand
balance `∑ xh = x° + ∑ yl` holds (11.14), and the price vector `p` is nonnegative (11.12). -/
def IsContEquilibrium {H K L : Type*} [Fintype H] [Fintype K] [Fintype L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x0 : K → ℤ)
    (x : H → (K → ℝ)) (y : L → (K → ℝ)) (p : K → ℝ) : Prop :=
  (∀ h : H, x h ∈ ContDemandSet (U h) p) ∧
  (∀ l : L, y l ∈ ContSupplySet (C l) p) ∧
  (∑ h, x h) = (fun k => (x0 k : ℝ)) + ∑ l, y l ∧
  (∀ k : K, 0 ≤ p k)

end DiscreteConvex.EconomicEquilibrium


