-- Prove2me | Definitions.Def_CrossLearnCB_UCB1CL_Supplement_Bidding
-- name    : CrossLearnCB_UCB1CL_Supplement_Bidding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T04:49:57.851805+00:00
-- url     : https://prove2.me/theorems/9cd71991-632e-4327-bb48-58d4d2e46f7e
-- title:
--   §5.2 and Appendix B, pp. 30, 43–44 — continuous bids, binary feedback, i.i.d. competing bids and fixed-value regret
-- statement:
--   A bid $b$ and the highest competing bid $h$ lie in $[0,1]$. With value $v$, the utility is $(v-b)\mathbb1\{b\ge h\}$. For Theorem 10 the value is fixed at $1$, so
--   $$u(b,h)=(1-b)\mathbb1\{b\ge h\}.$$
--   A policy chooses a bid from its own past bids, past win/loss observations, and a private random seed independent of the competing bids. It knows the horizon. Highest competing bids are independent draws from an unknown law $F$ on $[0,1]$. The best fixed bid has expected utility $\sup_{b\in[0,1]}\mathbb E_F u(b,h)$; regret is $T$ times this value minus the policy's expected cumulative utility. This is the binary-feedback first-price auction of Theorem 10, with no discretization.
--
--   **Formalization Note** Bids are the subtype `Icc 0 1`. The policy is jointly measurable in history and an arbitrary probability-space seed; this represents randomized algorithms, including remembered private randomness. `bidHistory` reveals no current or future competing bid, and the joint law is the product of the seed law and the finite i.i.d. competing-bid law. The supremum set is nonempty and bounded in $[0,1]$ for a probability law, so the real supremum is genuine. The source benchmark can equivalently use its maximizing bid: the bounded interval and the upper semicontinuous function $(1-b)F([0,b])$ ensure attainment. Padding the table after $T$ is never read in the sum.
-- source:
--   Balseiro et al., Contextual Bandits with Cross-Learning, arXiv:1809.09582v3, p. 30, §5.2; pp. 43–44, Appendix B, Theorem 10

import Mathlib

namespace CrossLearnCB.UCB1CL.Supplement

open MeasureTheory

/-- The continuum of admissible bids (and highest competing bids), pp. 30, 44. -/
abbrev Bid := Set.Icc (0 : ℝ) 1

/-- A bid policy sees its own past bids, win/loss observations, and a private random seed.
T is known when the policy is chosen. The bidder value is fixed at 1. -/
abbrev BidPolicy (Ω : Type*) := (t : ℕ) → (Fin t → Bid × Bool) → Ω → Bid

/-- Joint measurability makes expectations of randomized bidding policies genuine. -/
def BidPolicy.IsMeasurable {Ω : Type*} [MeasurableSpace Ω] (A : BidPolicy Ω) : Prop :=
  ∀ t, Measurable (fun z : (Fin t → Bid × Bool) × Ω => A t z.1 z.2)

/-- First-price utility at value v, with ties won (p. 30). -/
noncomputable def auctionUtility (v b h : Bid) : ℝ :=
  if (h : ℝ) ≤ (b : ℝ) then (v : ℝ) - (b : ℝ) else 0

/-- The fixed-value specialization used by Theorem 10. -/
noncomputable def bidUtility (b h : Bid) : ℝ :=
  auctionUtility ⟨1, by norm_num⟩ b h

/-- Replay only past win/loss feedback; the current competing bid is never an input to A. -/
noncomputable def bidHistory {Ω : Type*} (A : BidPolicy Ω) (seed : Ω) (h : ℕ → Bid) :
    (t : ℕ) → Fin t → Bid × Bool
  | 0 => Fin.elim0
  | t + 1 =>
    let old := bidHistory A seed h t
    let b := A t old seed
    Fin.lastCases (b, decide ((h t : ℝ) ≤ (b : ℝ))) old

/-- Expected utility of one fixed bid against an unknown i.i.d. competing-bid law. -/
noncomputable def bidRevenue (F : Measure Bid) (b : Bid) : ℝ :=
  ∫ h, bidUtility b h ∂F

/-- Best fixed bid: a bounded nonempty supremum (utilities lie in [0,1]). -/
noncomputable def bidOptimalRevenue (F : Measure Bid) : ℝ :=
  sSup (Set.range (bidRevenue F))

/-- Expected total utility with private seed independent of all i.i.d. highest competing bids.
The finite table is padded only after the horizon; that padding is never observed. -/
noncomputable def bidAlgorithmRevenue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : BidPolicy Ω) (F : Measure Bid) (T : ℕ) : ℝ :=
  ∫ z : Ω × (Fin T → Bid),
    let h : ℕ → Bid := fun n => if hn : n < T then z.2 ⟨n, hn⟩ else ⟨0, by norm_num⟩
    ∑ t : Fin T, bidUtility (A t (bidHistory A z.1 h t) z.1) (h t)
    ∂(μ.prod (Measure.pi (fun _ : Fin T => F)))

end CrossLearnCB.UCB1CL.Supplement


