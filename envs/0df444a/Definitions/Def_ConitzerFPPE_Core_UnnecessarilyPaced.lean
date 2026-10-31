-- Prove2me | Definitions.Def_ConitzerFPPE_Core_UnnecessarilyPaced
-- name    : ConitzerFPPE_Core_UnnecessarilyPaced
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:00:09.938127+00:00
-- url     : https://prove2.me/theorems/f8fc8453-67c8-4d96-8cc7-57bb4bb4e18b
-- title:
--   Unnecessarily paced bidder
-- statement:
--   For a finite market, multiplier vector $\alpha$, allocation $x$ and bidder $i$, unnecessary pacing means
--   $$s_i(\alpha,x)<B_i\quad\text{and}\quad\alpha_i<1.$$
--   BFPM feasibility is a separate condition. Both inequalities are strict.
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Definition 2 and preceding paragraph, p. 9; Lemmas 2–3, pp. 10–11; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_spend

namespace ConitzerFPPE.Core

def UnnecessarilyPaced {N M : Type*} [Fintype N] [Fintype M] (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ) (i : N) : Prop :=
  spend P α x i < P.B i ∧ α i < 1

end ConitzerFPPE.Core


