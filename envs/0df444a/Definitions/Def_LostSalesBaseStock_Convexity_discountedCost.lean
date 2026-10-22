-- Prove2me | Definitions.Def_LostSalesBaseStock_Convexity_discountedCost
-- name    : LostSalesBaseStock_Convexity_discountedCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T04:57:04.976195+00:00
-- url     : https://prove2.me/theorems/db83bd2e-ac55-4a25-986d-6bdbe7338003
-- title:
--   Discounted cost (3.1) of the order-up-to-$S$ policy
-- statement:
--   With the dynamics of the order-up-to-$S$ lost-sales system (end-of-period inventory position $\pi_n(S)$, end-of-period inventory on hand $i_n(S)$, lost sales $l_n(S)$), a holding cost $h_1$ per unit of inventory position, a storage cost $h_2$ per unit on hand at the end of each period, a lost-sales cost $p$ per unit of lost demand and a discount factor $\alpha$, the discounted cost over periods $0, \dots, N$ is
--
--   $$
--   C_N(S) = \sum_{n=0}^{N} \alpha^n \big( h_1 \, \pi_n(S) + h_2 \, i_n(S) + p \, l_n(S) \big).
--   $$
--
--   This is the paper's objective (3.1) for a given realization of lead times and demands. Purchase costs are omitted, as in the paper, which argues that with linear purchase costs and complete salvage they can be taken to be zero.
--
--   **Formalization Note** The definition takes $\alpha, h_1, h_2, p$ as arbitrary reals; the paper's standing restrictions $0 < \alpha \le 1$ and $h_1, h_2, p \ge 0$ are hypotheses of the theorems.
-- source:
--   Janakiraman and Roundy, Lost-Sales Problems with Stochastic Lead Times: Convexity Results for Base-Stock Policies, Oper. Res. 52(5) (2004), p. 797, Eq. (3.1)

import Mathlib
import Definitions.Def_LostSalesBaseStock_Convexity_dynamics

namespace LostSalesBaseStock.Convexity

/-- Discounted cost (3.1) of the order-up-to-`S` policy over periods `0, …, N`
(Janakiraman–Roundy 2004, p. 797): `∑_{n=0}^{N} α^n (h₁ π_n + h₂ i_n + p l_n)`, with holding
cost `h₁` on the end-of-period inventory position, storage cost `h₂` on the end-of-period
inventory on hand, lost-sales cost `p`, and discount factor `α`. -/
noncomputable def discountedCost (lam : ℕ → ℕ) (D : ℕ → ℝ) (N : ℕ) (α h₁ h₂ p : ℝ) (S : ℝ) :
    ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    α ^ n * (h₁ * invPosition lam D S n + h₂ * endOnHand lam D S n + p * lostSales lam D S n)

end LostSalesBaseStock.Convexity


