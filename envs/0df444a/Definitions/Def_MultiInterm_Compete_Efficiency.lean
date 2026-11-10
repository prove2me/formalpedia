-- Prove2me | Definitions.Def_MultiInterm_Compete_Efficiency
-- name    : MultiInterm_Compete_Efficiency
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:42:29.152204+00:00
-- url     : https://prove2.me/theorems/bafb98cd-0e0d-43a3-888b-fbc3e36a228e
-- title:
--   Threshold allocation, downstream efficiency, relevance and auction implementation
-- statement:
--   An outcome is surplus-optimal up to threshold $\tau\ge0$ if almost surely the highest-valued bidder receives the item when its value exceeds $\tau$, and otherwise the item is unallocated. Surplus optimality without a threshold means almost-sure allocation to a highest-valued bidder. Atomlessness makes that bidder unique almost surely.
--
--   Downstream efficiency means that the downstream slot assignment maximizes the sum of upstream bidder utilities, averaging over upstream tie-breaking, among feasible slot assignments and attached bids. Relevance means that some bid meets the intermediary's reserve with positive probability. Effective participation at threshold $\tau$ means that types below $\tau$ meet neither reserve, whereas types above $\tau$ meet at least one almost surely.
--
--   Implementing an ordinary second-price auction with reserve $r_\theta$ means the composite winner is a possible truthful second-price winner, its individual downstream payments at $\theta$ equal that auction's payments, and every upstream payment is zero, almost surely. This is an outcome property, not a requirement of truthful bidding.
--
--   Total surplus and deadweight loss are nonnegative expectations:
--   $$S_{\rm tot}=\mathbb E[v_W],\qquad L=\mathbb E[\max_i v_i-v_W],$$
--   where $v_W=0$ if there is no winner. The lost-value definition agrees with the difference of expected surpluses whenever that difference is defined and remains meaningful for infinite means.
--
--   **Formalization Note** No conclusion is assumed in the definition of equilibrium. Effective participation follows Appendix C.4's explicit allowance for bids below the reserve. Efficiency compares feasible allocations of two slots and arbitrary upstream bids; giving both slots to a highest-valued bidder with a zero upstream bid realizes the maximum possible upstream utility.
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), pp. 10–12 (PDF 11–13), Definitions 3.2–3.4 and §5.1; pp. 16–17 (PDF 17–18), Definition 6.5, relevance and Lemma 6.7; pp. 41–42 (PDF 42–43), Appendix C.4

import Definitions.Def_MultiInterm_Compete_Equilibrium

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

def Highest {n : ℕ} (z : Observation n) (i : Fin n) : Prop :=
  ∀ j, (z j).1 ≤ (z i).1

/-- Highest value is awarded the item above τ, and there is no sale at or below τ. -/
def ThresholdOptimal (D : ValueDistribution) (n : ℕ) (s : BidderStrategy)
    (r : Reserves) (τ : ℝ≥0) : Prop :=
  AlmostSurely D n s r fun z _ u =>
    (∃ i, τ < (z i).1 ∧ Highest z i ∧ u = some i) ∨
    ((∀ i, (z i).1 ≤ τ) ∧ u = none)

/-- Surplus optimality means efficient allocation almost surely, not only equality
of two potentially infinite expected surpluses. -/
def SurplusOptimal (D : ValueDistribution) (n : ℕ) (s : BidderStrategy)
    (r : Reserves) : Prop :=
  AlmostSurely D n s r fun z _ u => ∃ i, Highest z i ∧ u = some i

/-- Expected total upstream utility for an arbitrary allocation of the two slots
and arbitrary attached bids, averaging over upstream tie-breaking. -/
noncomputable def upstreamSurplus {n : ℕ} (v : Fin n → ℝ≥0)
    (a : Fin n → Action) (w : Winners n) : ℝ := by
  classical
  exact ∑ u : Option (Fin n), (spaWeight 0 (upstreamBids a w) u).toReal *
    ((match u with | none => 0 | some i => (v i : ℝ)) -
      (spaPrice 0 (upstreamBids a w) u : ℝ))

/-- Downstream winners maximize the total upstream utility over feasible slot
allocations and upstream bids, as in §5.1. -/
def DownstreamEfficient (D : ValueDistribution) (n : ℕ) (s : BidderStrategy)
    (r : Reserves) : Prop :=
  AlmostSurely D n s r fun z w _ => ∀ (a' : Fin n → Action) (w' : Winners n),
    upstreamSurplus (fun i => (z i).1) a' w' ≤
      upstreamSurplus (fun i => (z i).1) (fun i => (z i).2) w

/-- Positive probability that some submitted bid meets the reserve. -/
def Relevant (D : ValueDistribution) (n : ℕ) (s : BidderStrategy)
    (r : Reserves) (θ : Bool) : Prop :=
  0 < (profileLaw D (fun _ : Fin n => s)) {z | ∃ i, Meets (r θ) (downstreamBids z θ i)}

/-- Participation means effective entry (meeting a reserve), consistently with C.4's
"abstains (or bids below the reserve)". Types exactly at τ are unrestricted. -/
def ThresholdParticipation (D : ValueDistribution) (s : BidderStrategy)
    (r : Reserves) (τ : ℝ≥0) : Prop :=
  ∀ᵐ v ∂D.law, ∀ᵐ a ∂s.kernel v,
    (v < τ → ∀ θ, ¬ Meets (r θ) ((a θ).map Prod.fst)) ∧
    (τ < v → ∃ θ, Meets (r θ) ((a θ).map Prod.fst))

/-- Implementation of the ordinary truthful second-price auction at the given reserve:
same winner and per-bidder downstream payments, with zero upstream payments. -/
def OrdinarySecondPrice (D : ValueDistribution) (n : ℕ) (s : BidderStrategy)
    (r : Reserves) (θ : Bool) : Prop :=
  AlmostSurely D n s r fun z w u =>
    0 < spaWeight (r θ) (fun i => some (z i).1) u ∧
    (∀ i, downstreamPayment r z w θ i =
      spaPayment (r θ) (fun j => some (z j).1) u i) ∧
    (∀ i, upstreamPayment z w u i = 0)

/-- Expected generated value, allowing +∞. -/
noncomputable def totalSurplus (D : ValueDistribution) (n : ℕ)
    (s : BidderStrategy) (r : Reserves) : ℝ≥0∞ :=
  ∫⁻ z, auctionExpectation r z (fun _ u => match u with
    | none => 0 | some i => ((z i).1 : ℝ≥0∞)) ∂profileLaw D (fun _ : Fin n => s)

/-- Expected ex-post lost value; agrees with S* - S when that difference is defined
and remains meaningful when both expectations are infinite. -/
noncomputable def deadweightLoss (D : ValueDistribution) (n : ℕ)
    (s : BidderStrategy) (r : Reserves) : ℝ≥0∞ :=
  ∫⁻ z, auctionExpectation r z (fun _ u =>
    ((Finset.univ.sup (fun i => (z i).1) -
      (match u with | none => 0 | some i => (z i).1) : ℝ≥0) : ℝ≥0∞))
    ∂profileLaw D (fun _ : Fin n => s)

end MultiInterm.Compete


