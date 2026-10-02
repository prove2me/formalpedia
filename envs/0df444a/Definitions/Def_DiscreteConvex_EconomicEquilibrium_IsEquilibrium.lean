-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsEquilibrium
-- name    : DiscreteConvex_EconomicEquilibrium_IsEquilibrium
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:07:54.32998+00:00
-- url     : https://prove2.me/theorems/8b792dd0-cebf-4bd0-9024-7e15f27607fa
-- title:
--   Competitive equilibrium (Eqs. 11.9-11.12)
-- statement:
--   $((x_h \mid h \in H), (y_l \mid l \in L), p)$ is an **equilibrium** (or competitive equilibrium) for total initial endowment $x^\circ \in \mathbb Z^K$ (Eqs. (11.9)-(11.12)): every consumer's allocation $x_h$ lies in her demand set $D_h(p)$ (11.9), every producer's allocation $y_l$ lies in his supply set $S_l(p)$ (11.10), the supply-demand balance $\sum_h x_h = x^\circ + \sum_l y_l$ holds (11.11, rewritten as (11.14)), and the price vector $p$ is nonnegative (11.12).
--
--   **Formalization Note.** An exchange economy (no producers) is the special case $L = \mathrm{PEmpty}$, used for the goal theorem (11.13); the middle conjunct and the sum over $L$ are then vacuous.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.325-326, Eqs. (11.9)-(11.12).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, pp.325-326, Eqs. (11.9)-(11.12)

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_DemandSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_SupplySet

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, pp.325-326, Eqs. (11.9)-(11.12): a competitive
equilibrium of the economy with indivisible commodities, in
`DiscreteConvex.EconomicEquilibrium`.
-/

namespace DiscreteConvex.EconomicEquilibrium

/-- `((xh | h ∈ H), (yl | l ∈ L), p)` is an **equilibrium** (or competitive equilibrium) for total
initial endowment `x° ∈ Zᴷ` (Eqs. (11.9)-(11.12)): every consumer's allocation `x h` lies in her
demand set `Dh(p)` (11.9), every producer's allocation `y l` lies in his supply set `Sl(p)`
(11.10), the supply-demand balance `∑ xh = x° + ∑ yl` holds (11.11, rewritten as (11.14)), and the
price vector `p` is nonnegative (11.12). An exchange economy (no producers) is the special case
`L = PEmpty` (so the middle conjunct and the sum over `L` are vacuous). -/
def IsEquilibrium {H K L : Type*} [Fintype H] [Fintype K] [Fintype L]
    (U : H → (K → ℤ) → WithBot ℝ) (C : L → (K → ℤ) → WithTop ℝ) (x0 : K → ℤ)
    (x : H → (K → ℤ)) (y : L → (K → ℤ)) (p : K → ℝ) : Prop :=
  (∀ h : H, x h ∈ DemandSet (U h) p) ∧
  (∀ l : L, y l ∈ SupplySet (C l) p) ∧
  (∑ h, x h) = x0 + ∑ l, y l ∧
  (∀ k : K, 0 ≤ p k)

end DiscreteConvex.EconomicEquilibrium


