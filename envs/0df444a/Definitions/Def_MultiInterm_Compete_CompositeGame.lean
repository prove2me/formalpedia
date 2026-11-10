-- Prove2me | Definitions.Def_MultiInterm_Compete_CompositeGame
-- name    : MultiInterm_Compete_CompositeGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:41:02.668585+00:00
-- url     : https://prove2.me/theorems/6d60b9a9-050b-4c19-9192-2cf875385770
-- title:
--   The composite auction: two intermediaries, attached upstream bids, payments and expectations
-- statement:
--   Alice and Bob choose nonnegative reserves. Each bidder chooses an action at each intermediary: abstain, or submit a nonnegative downstream bid with an optional nonnegative upstream bid. A bidder may use either, neither, or both intermediaries. The two downstream second-price auctions select winners independently with uniform tie-breaking. Only each winner's attachment is forwarded.
--
--   For each bidder, merge its forwarded bids by retaining the larger, with absence retained when neither attachment is present. These retained bids enter an upstream second-price auction with reserve zero. A sole forwarded bidder wins for free. Different bidders' tied bids are broken uniformly. All downstream payments are charged even if their payer loses upstream.
--
--   The realized utility is $v_iX_i^{\rm up}-P_i^A-P_i^B-P_i^{\rm up}$ and intermediary $\theta$ receives $\sum_iP_i^\theta$. Conditional on bidder $i$ having value $v$, interim expected utility is
--   $$U_i(v)=\mathbb E[vX_i^{\rm up}\mid v]-\mathbb E[P_i^A+P_i^B+P_i^{\rm up}\mid v].$$
--   Values are independent with law $D$, and bidders' actions are independent conditional on their own values. Expectations also average over all three tie-breaks. The continuation game instantiates the separate Bayesian-game definition using this actual payoff.
--
--   **Formalization Note** A single identity and one optional upstream attachment per downstream bid encode footnote 4 and own-bid merging; the maximum of a nonempty finite bundle is its effective bid. Attachments are unrestricted, and bids need not be truthful or below value. The benefit integral is bounded by the fixed finite type $v$; an infinite payment gives utility $-\infty$ without any $\infty-\infty$ subtraction. The sample measure is a finite product of value–action kernel composition products. Finite weighted sums integrate tie-breaking, and almost-sure outcome predicates include every outcome with positive conditional weight.
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), pp. 9–10 (PDF 10–11), Definition 3.1 and utilities; p. 13 (PDF 14), own-bid merging

import Definitions.Def_MultiInterm_Compete_BayesianGame
import Definitions.Def_MultiInterm_Compete_SecondPrice
import Definitions.Def_MultiInterm_Compete_ValueDistribution

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

/-- false = Alice; true = Bob. Each submitted bid carries zero or one upstream bid. -/
abbrev Action := Bool → Option (ℝ≥0 × Option ℝ≥0)
abbrev Reserves := Bool → ℝ≥0
abbrev BidderStrategy := MixedStrategy ℝ≥0 Action
abbrev SymmetricStrategy := Reserves → BidderStrategy
abbrev Observation (n : ℕ) := Fin n → ℝ≥0 × Action
abbrev Winners (n : ℕ) := Bool → Option (Fin n)

noncomputable def downstreamBids {n : ℕ} (z : Observation n) (θ : Bool) : Fin n → Option ℝ≥0 :=
  fun i => ((z i).2 θ).map Prod.fst

/-- Own bids are merged by their maximum, retaining absence when both are absent. -/
def mergeOwn : Option ℝ≥0 → Option ℝ≥0 → Option ℝ≥0
  | none, q => q
  | p, none => p
  | some a, some b => some (max a b)

noncomputable def forwarded {n : ℕ} (a : Fin n → Action) (w : Winners n)
    (θ : Bool) (i : Fin n) : Option ℝ≥0 := by
  classical
  exact if w θ = some i then (a i θ).bind Prod.snd else none

noncomputable def upstreamBids {n : ℕ} (a : Fin n → Action) (w : Winners n) :
    Fin n → Option ℝ≥0 :=
  fun i => mergeOwn (forwarded a w false i) (forwarded a w true i)

/-- Independent uniform tie-breaking in the two downstream auctions and upstream. -/
noncomputable def outcomeWeight {n : ℕ} (r : Reserves) (z : Observation n)
    (w : Winners n) (u : Option (Fin n)) : ℝ≥0∞ :=
  spaWeight (r false) (downstreamBids z false) (w false) *
  spaWeight (r true) (downstreamBids z true) (w true) *
  spaWeight 0 (upstreamBids (fun i => (z i).2) w) u

noncomputable def downstreamPayment {n : ℕ} (r : Reserves) (z : Observation n)
    (w : Winners n) (θ : Bool) (i : Fin n) : ℝ≥0 :=
  spaPayment (r θ) (downstreamBids z θ) (w θ) i

noncomputable def upstreamPayment {n : ℕ} (z : Observation n)
    (w : Winners n) (u : Option (Fin n)) (i : Fin n) : ℝ≥0 :=
  spaPayment 0 (upstreamBids (fun j => (z j).2) w) u i

noncomputable def totalPayment {n : ℕ} (r : Reserves) (z : Observation n)
    (w : Winners n) (u : Option (Fin n)) (i : Fin n) : ℝ≥0 :=
  downstreamPayment r z w false i + downstreamPayment r z w true i +
    upstreamPayment z w u i

/-- Expectation over the finite outcome set; the probability is the actual auction rule. -/
noncomputable def auctionExpectation {n : ℕ} (r : Reserves) (z : Observation n)
    (f : Winners n → Option (Fin n) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ w, ∑ u, outcomeWeight r z w u * f w u

/-- IID values, and independent mixed actions conditional on each bidder's own value. -/
noncomputable def profileLaw (D : ValueDistribution) {n : ℕ}
    (p : Fin n → BidderStrategy) : Measure (Observation n) :=
  Measure.pi fun i => D.law ⊗ₘ (p i).kernel

/-- Conditional law when bidder i has value v and chooses an arbitrary mixed action. -/
noncomputable def deviationLaw (D : ValueDistribution) {n : ℕ}
    (p : Fin n → BidderStrategy) (i : Fin n) (v : ℝ≥0) (d : ProbabilityMeasure Action) :
    Measure (Observation n) := by
  classical
  exact Measure.pi fun j => if j = i then (Measure.dirac v).prod (d : Measure Action)
    else D.law ⊗ₘ (p j).kernel

/-- Interim utility: the benefit integral is at most v, whereas payments can be infinite.
Consequently finite benefit minus infinite cost is -∞, never an undefined ∞-∞. -/
noncomputable def interimUtility (D : ValueDistribution) {n : ℕ} (r : Reserves)
    (i : Fin n) (v : ℝ≥0) (p : Fin n → BidderStrategy) (d : ProbabilityMeasure Action) : EReal := by
  classical
  let μ := deviationLaw D p i v d
  exact (∫⁻ z, auctionExpectation r z (fun _ u => if u = some i then (v : ℝ≥0∞) else 0) ∂μ).toEReal -
    (∫⁻ z, auctionExpectation r z (fun w u => (totalPayment r z w u i : ℝ≥0∞)) ∂μ).toEReal

/-- The concrete continuation game, an instance of the separate general Bayesian game. -/
noncomputable def CompositeGame (D : ValueDistribution) (n : ℕ) (r : Reserves) :
    BayesianGame (Fin n) ℝ≥0 Action where
  types := D.Types
  payoff := interimUtility D r

noncomputable def revenue (D : ValueDistribution) (n : ℕ) (s : BidderStrategy)
    (r : Reserves) (θ : Bool) : ℝ≥0∞ :=
  ∫⁻ z, auctionExpectation r z (fun w _ => ∑ i, (downstreamPayment r z w θ i : ℝ≥0∞))
    ∂profileLaw D (fun _ : Fin n => s)

noncomputable def totalRevenue (D : ValueDistribution) (n : ℕ) (s : BidderStrategy)
    (r : Reserves) : ℝ≥0∞ :=
  ∫⁻ z, auctionExpectation r z (fun w u => ∑ i, (totalPayment r z w u i : ℝ≥0∞))
    ∂profileLaw D (fun _ : Fin n => s)

/-- An almost-sure outcome property, including every tie outcome of positive probability. -/
def AlmostSurely (D : ValueDistribution) (n : ℕ) (s : BidderStrategy) (r : Reserves)
    (P : Observation n → Winners n → Option (Fin n) → Prop) : Prop :=
  ∀ᵐ z ∂profileLaw D (fun _ : Fin n => s), ∀ w u, 0 < outcomeWeight r z w u → P z w u

end MultiInterm.Compete


