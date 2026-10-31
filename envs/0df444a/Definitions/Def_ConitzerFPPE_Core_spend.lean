-- Prove2me | Definitions.Def_ConitzerFPPE_Core_spend
-- name    : ConitzerFPPE_Core_spend
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T18:59:18.092982+00:00
-- url     : https://prove2.me/theorems/6fc75663-4ad1-43d9-a483-77c62f0c4eb0
-- title:
--   Bidder expenditure
-- statement:
--   For a finite market, real multiplier vector $\alpha$ and real allocation $x$, bidder $i$ spends
--   $$s_i(\alpha,x)=\sum_{j\in M}x_{ij}p_j(\alpha).$$
--   Here $p_j$ is the highest paced bid with zero adjoined. The empty sum is zero. Feasibility is imposed separately.
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Definition 1 (budget-feasible clause), p. 9; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_price

namespace ConitzerFPPE.Core

noncomputable def spend {N M : Type*} [Fintype N] [Fintype M] (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ) (i : N) : ℝ :=
  ∑ j, x i j * price P α j

end ConitzerFPPE.Core


