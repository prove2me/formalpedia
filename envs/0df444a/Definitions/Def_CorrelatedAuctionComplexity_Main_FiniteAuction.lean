-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_FiniteAuction
-- name    : CorrelatedAuctionComplexity_Main_FiniteAuction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:35.518862+00:00
-- url     : https://prove2.me/theorems/8f87bf92-34b0-4363-9ff9-345feb3da7d7
-- title:
--   Finite lotteries and a single first-price auction
-- statement:
--   For a finite participant set $S$, a value vector $v$, and submitted bids $b$, let $h_S(b)$ be the participants whose bid is at least every other participant's bid. The single-item first-price payoff is
--
--   $$u_i^S(b)=\begin{cases}(v_i-b_i)/|h_S(b)|,&i\in h_S(b),\0,&\text{otherwise}.\end{cases}$$
--
--   All participants tied at the highest bid count, including zero-valued bidders. A weighted auction is a nonempty participant set with a positive rational weight. Lotteries and independent joint probabilities reuse the published finite-game vocabulary; expectation is the finite sum over independent action profiles. This common auction outcome is used by both models.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Section 3, pp. 8–11 (PDF pp. 8–11)

import Mathlib
import Definitions.Def_agt_games

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


/-- A lottery has nonnegative real weights of total mass one. -/
abbrev IsLottery {B : Type} [Fintype B] (p : B → ℝ) : Prop := AGT.IsLottery p

/-- Independent randomization, conditional on the already fixed values. -/
noncomputable def expectation {N B : Type} [Fintype N] [DecidableEq N] [Fintype B]
    (p : N → B → ℝ) (u : (N → B) → ℝ) : ℝ :=
  ∑ b : N → B, AGT.profileProb p b * u b

noncomputable def deviation {N B : Type} [Fintype N] [DecidableEq N]
    [Fintype B] [DecidableEq B] (p : N → B → ℝ) (i : N) (b : B) : N → B → ℝ :=
  Function.update p i (fun a => if a = b then 1 else 0)

/-- A single first-price auction on the listed participants; all tied highest bidders count. -/
def singlePayoff {N : Type} [DecidableEq N] (S : Finset N)
    (v : N → ℚ) (b : N → ℚ) (i : N) : ℚ :=
  if i ∈ S ∧ ∀ j ∈ S, b j ≤ b i then
    (v i - b i) / ((S.filter fun j => ∀ k ∈ S, b k ≤ b j).card : ℚ)
  else 0

structure AuctionEdge (N : Type) where
  participants : Finset N
  weight : ℚ

/-- The same single-auction model is shared by DFPA and HDFPA. -/
def AuctionEdge.WellFormed {N : Type} (e : AuctionEdge N) : Prop :=
  e.participants.Nonempty ∧ 0 < e.weight

end CorrelatedAuctionComplexity.Main


