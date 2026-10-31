-- Prove2me | Definitions.Def_ConitzerFPPE_Core_revenue
-- name    : ConitzerFPPE_Core_revenue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:00:12.730316+00:00
-- url     : https://prove2.me/theorems/10ea10e4-314a-4d44-ba56-a76ce9934ef1
-- title:
--   Seller revenue
-- statement:
--   For a finite market and real vectors $\alpha,x$, seller revenue is actual total expenditure:
--   $$\operatorname{Rev}(\alpha,x)=\sum_{i\in N}s_i(\alpha,x)=\sum_{i\in N}\sum_{j\in M}x_{ij}p_j(\alpha).$$
--   An empty sum is zero. This definition does not assume full sale or replace payments by welfare.
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, §2.1, revenue notation p. 11; Lemma 4, p. 12; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_spend

namespace ConitzerFPPE.Core

noncomputable def revenue {N M : Type*} [Fintype N] [Fintype M] (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ) : ℝ :=
  ∑ i, spend P α x i

end ConitzerFPPE.Core


