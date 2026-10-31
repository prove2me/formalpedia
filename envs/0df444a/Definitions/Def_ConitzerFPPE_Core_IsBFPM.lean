-- Prove2me | Definitions.Def_ConitzerFPPE_Core_IsBFPM
-- name    : ConitzerFPPE_Core_IsBFPM
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:00:07.180798+00:00
-- url     : https://prove2.me/theorems/6b2c9fb4-b949-4c65-815a-7c6a9e53b12e
-- title:
--   Definition 1 — Budget-feasible first-price pacing multipliers
-- statement:
--   A budget-feasible first-price pacing pair $(\alpha,x)$ in a finite market with $v_{ij}\ge0$ and $B_i>0$ has $0\le\alpha_i\le1$ and $0\le x_{ij}\le1$. Prices are $p_j=\max(\{0\}\cup\{\alpha_i v_{ij}:i\in N\})$. A positive allocation implies $\alpha_i v_{ij}=p_j$; each bidder's expenditure satisfies $s_i\le B_i$; every positive-price good satisfies $\sum_i x_{ij}=1$; and every good satisfies $\sum_i x_{ij}\le1$. Fractional ties and zero valuations are allowed. Zero-price goods may remain unsold. Empty finite sets are allowed, with zero prices for no bidders and zero empty sums. These are feasibility conditions only.
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Definition 1, p. 9; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_spend

namespace ConitzerFPPE.Core

structure IsBFPM {N M : Type*} [Fintype N] [Fintype M] (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ) : Prop where
  multiplier_bounds : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1
  allocation_bounds : ∀ i j, x i j ∈ Set.Icc (0 : ℝ) 1
  highest_bidder : ∀ i j, 0 < x i j → α i * P.v i j = price P α j
  budget_feasible : ∀ i, spend P α x i ≤ P.B i
  positive_price_clearance : ∀ j, 0 < price P α j → ∑ i, x i j = 1
  no_overselling : ∀ j, ∑ i, x i j ≤ 1

end ConitzerFPPE.Core


