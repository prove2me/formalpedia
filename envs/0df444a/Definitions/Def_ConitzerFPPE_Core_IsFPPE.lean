-- Prove2me | Definitions.Def_ConitzerFPPE_Core_IsFPPE
-- name    : ConitzerFPPE_Core_IsFPPE
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:01:18.786931+00:00
-- url     : https://prove2.me/theorems/8a59f8d3-f360-4a01-9569-0f8fef8f69d9
-- title:
--   Definition 2 — First-price pacing equilibrium
-- statement:
--   A first-price pacing equilibrium is a budget-feasible first-price pacing pair $(\alpha,x)$ satisfying
--   $$\forall i\in N,\quad s_i(\alpha,x)<B_i\ \Longrightarrow\ \alpha_i=1.$$
--   An unpaced bidder may have either a tight or a slack budget. There is no extra best-response, maximality or revenue-optimality condition. The finite market, price and empty-set conventions are those of BFPM.
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Definition 2, p. 9; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_IsBFPM

namespace ConitzerFPPE.Core

def IsFPPE {N M : Type*} [Fintype N] [Fintype M] (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ) : Prop :=
  IsBFPM P α x ∧ ∀ i, spend P α x i < P.B i → α i = 1

end ConitzerFPPE.Core


