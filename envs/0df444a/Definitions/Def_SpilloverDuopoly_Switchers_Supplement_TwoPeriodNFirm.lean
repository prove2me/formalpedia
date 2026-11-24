-- Prove2me | Definitions.Def_SpilloverDuopoly_Switchers_Supplement_TwoPeriodNFirm
-- name    : SpilloverDuopoly_Switchers_Supplement_TwoPeriodNFirm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:37:10.496411+00:00
-- url     : https://prove2.me/theorems/9cbcebc0-eb72-470e-abee-8a9b9733a480
-- title:
--   Appendix D.1, pp. 50–51 — the two-period N-firm experience-goods game: second-period segment games, profits and symmetric equilibrium
-- statement:
--   The two-period game with $N$ firms of Appendix D.1. In the first period firms set prices $p_1,\dots,p_N$ and consumers buy the cheapest acceptable product, with market shares $\lambda_j(p)$ given by the first-period share rule. In the second period every firm makes an offer to the segment $k$ of consumers who bought product $k$ in the first period: firm $k$'s offer is its price to repeat consumers, the others' are prices to switchers. The segment's demand $d_k$, per unit of $\lambda_k$, treats the $N-1$ products it has not tried as perfect substitutes.
--
--   Firm $j$'s second-period profit from segment $k$ at offers $o$ is $(o_j-c)\,d_k(o)(j)$. A **second-period equilibrium** is a family of offers $o_2(k)$, one per segment, each a pure Nash equilibrium of its segment game; $\pi_j^k$ denotes firm $j$'s profit there, per unit of $\lambda_k$. Firm $i$'s profit in the two-stage game is
--
--   $$
--   \Pi_i(p)=\lambda_i(p)\,(p_i-c)+\delta\sum_{k=1}^N\lambda_k(p)\,\pi_i^k .
--   $$
--
--   A **symmetric equilibrium** at the price $p$ is a profile in which every firm charges $p$ and no firm gains by a unilateral deviation to any real price.
--
--   **Formalization Note** Second-period offers are a price or no sale. The second-period play is fixed while first-period prices vary: second-period profits per unit of share do not depend on first-period shares (p. 10).
-- source:
--   Chen, Stanton & Thomas, Information spillovers in experience goods competition, accepted manuscript (Management Science 70(6), 2024; LSE Research Online eprint 120790, version of June 18, 2023), pp. 50–51 (PDF 52–53), Appendix D.1, eq. (26), Theorem D.1

import Mathlib
import Definitions.Def_ImbalPricing_IsPureNash
import Definitions.Def_SpilloverDuopoly_Switchers_Supplement_PricingGames

namespace SpilloverDuopoly.Switchers.Supplement

open Finset

/-- The two-period `N`-firm experience-goods game of Appendix D.1 (pp. 50–51 (PDF 52–53)).
Besides the first-period data, `demand2 k` is the second-period demand of the segment of consumers
who bought product `k` in the first period, per unit of that segment's first-period share `λ_k`,
as a function of the second-period offers of all firms to that segment (firm `k`'s offer is its
repeat price `R_k`, the others' are switching prices `S_j`). -/
structure TwoPeriodNFirm (N : ℕ) extends FirstPeriod (Fin N) where
  demand2 : Fin N → SegmentDemand (Fin N)

namespace TwoPeriodNFirm

variable {N : ℕ}

/-- Standing assumptions: those of the first period, and for every first-period segment `k` the
`N - 1` products the segment has not tried are perfect substitutes for it. -/
def Standing (G : TwoPeriodNFirm N) : Prop :=
  G.toFirstPeriod.Standing ∧ ∀ k, UntriedSubstitutes (univ.erase k) (G.demand2 k)

/-- Firm `j`'s second-period profit from segment `k` at the offer profile `o`, per unit of `λ_k`. -/
def segProfit (G : TwoPeriodNFirm N) (k : Fin N) (o : Fin N → Offer) (j : Fin N) : ℝ :=
  margin G.c (o j) * G.demand2 k o (some j)

/-- Second-period equilibrium: for every first-period segment `k`, the offers `o2 k` to it are a
pure Nash equilibrium of the segment's pricing game (over all real prices and not selling). -/
def IsSecondEq (G : TwoPeriodNFirm N) (o2 : Fin N → Fin N → Offer) : Prop :=
  ∀ k, ImbalPricing.IsPureNash (fun _ => Set.univ) (fun j o => G.segProfit k o j) (o2 k)

/-- `π_j^k`: firm `j`'s second-period equilibrium profit from segment `k`, per unit of `λ_k`.
For `j = k` it is the profit from repeat consumers, for `j ≠ k` from switchers. -/
def piK (G : TwoPeriodNFirm N) (o2 : Fin N → Fin N → Offer) (k j : Fin N) : ℝ :=
  G.segProfit k (o2 k) j

/-- Firm `i`'s profit in the two-stage pricing game at first-period prices `p`, given the
second-period play `o2`: `λ_i (p_i - c) + δ ∑_k λ_k π_i^k`, with first-period shares `λ_k`. -/
noncomputable def profit (G : TwoPeriodNFirm N) (o2 : Fin N → Fin N → Offer) (p : Fin N → ℝ)
    (i : Fin N) : ℝ :=
  G.share p i * (p i - G.c) + G.delta * ∑ k, G.share p k * G.piK o2 k i

/-- A symmetric first-period equilibrium at the common price `p`: the profile in which every firm
charges `p` is a pure Nash equilibrium of the first-period game (all real prices) with payoffs
`profit o2`. -/
def IsSymEq (G : TwoPeriodNFirm N) (o2 : Fin N → Fin N → Offer) (p : ℝ) : Prop :=
  ImbalPricing.IsPureNash (fun _ => Set.univ) (fun i q => G.profit o2 q i) (fun _ => p)

end TwoPeriodNFirm

end SpilloverDuopoly.Switchers.Supplement


