-- Prove2me | Definitions.Def_ConitzerFPPE_Core_price
-- name    : ConitzerFPPE_Core_price
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T18:58:47.25975+00:00
-- url     : https://prove2.me/theorems/42d450de-8020-46d1-aaf6-3d01cad230ed
-- title:
--   First-price unit price
-- statement:
--   For a finite market with real nonnegative valuations $v_{ij}$ and positive budgets $B_i$, a real multiplier vector $\alpha$ gives unit price
--   $$p_j(\alpha)=\max\bigl(\{0\}\cup\{\alpha_i v_{ij}:i\in N\}\bigr).$$
--   For feasible multipliers and a nonempty bidder set this is the highest paced bid in Definition 1. The adjoined zero defines the price as zero when there are no bidders; for arbitrary negative, infeasible multipliers it also floors the price at zero. No equilibrium or optimality assumption enters this definition. Bidder and good labels are arbitrary finite types.
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Definition 1, p. 9; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_MultPacing_Existence_Model

namespace ConitzerFPPE.Core

noncomputable def price {N M : Type*} [Fintype N] [Fintype M] (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (j : M) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun k : Option N => match k with
      | none => 0
      | some i => α i * P.v i j)

end ConitzerFPPE.Core


