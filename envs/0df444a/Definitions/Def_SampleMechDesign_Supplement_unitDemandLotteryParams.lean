-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_unitDemandLotteryParams
-- name    : SampleMechDesign_Supplement_unitDemandLotteryParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:48:00.144204+00:00
-- url     : https://prove2.me/theorems/f5589d3a-8dce-48ff-a42e-0c012dd8b520
-- title:
--   Appendix A.1 — lottery parameters for a unit-demand buyer
-- statement:
--   Under a lottery $(\varphi^{(j)},p^{(j)})$ a unit-demand buyer receives only one item, item $i$ with probability $\varphi^{(j)}[i]$, so
--   $$
--   \varphi^{(j)}\in[0,1]^m,\qquad \sum_{i=1}^m\varphi^{(j)}[i]\le1\qquad(j=1,\dots,\ell).
--   $$
--   Her expected utility is $\sum_iv_1(e_i)\varphi^{(j)}[i]-p^{(j)}$, as for an additive buyer, so the class $\mathcal M'$ for a unit-demand buyer is the same function $\mathrm{profit}'$ on this smaller parameter set.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Appendix A.1, p.31 (PDF p.31)

import Mathlib
import Definitions.Def_SampleMechDesign_Supplement_lotteryProfit

namespace SampleMechDesign.Supplement

/-- **Lotteries for a unit-demand buyer.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6,
Appendix A.1, p.31.

Under a lottery `(φ^(j), p^(j))` a unit-demand buyer receives only one item, item `i` with
probability `φ^(j)[i]`, so `∑_i φ^(j)[i] ≤ 1`. Her expected utility is `∑_i v_1(e_i) φ^(j)[i] − p^(j)`,
as for an additive buyer, so the class `M′` is the same function `lotteryProfit′` restricted to
the parameter set

`unitDemandLotteryParams ℓ m = {p | φ^(j) ∈ [0, 1]^m and ∑_i φ^(j)[i] ≤ 1 for j = 1, …, ℓ}`. -/
def unitDemandLotteryParams (ℓ m : ℕ) : Set (Fin (ℓ * (m + 1)) → ℝ) :=
  {p | p ∈ lotteryParams ℓ m ∧ ∀ j : Fin ℓ, ∑ i, lotteryPhi p j.succ i ≤ 1}

end SampleMechDesign.Supplement


