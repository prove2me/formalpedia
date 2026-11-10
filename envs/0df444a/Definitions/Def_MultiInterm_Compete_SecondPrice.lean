-- Prove2me | Definitions.Def_MultiInterm_Compete_SecondPrice
-- name    : MultiInterm_Compete_SecondPrice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:39:59.885497+00:00
-- url     : https://prove2.me/theorems/3c3d2c44-f05c-4a67-b5fc-57f5293fed6d
-- title:
--   Second-price auctions with reserves, abstention and uniform random tie-breaking
-- statement:
--   For $n$ bidders, a bid is either absent or a nonnegative real number. A submitted bid meets reserve $r\ge0$ exactly when it is at least $r$. Among submitted bids meeting the reserve, choose a largest bid, uniformly among the tied bidders. If no bid meets the reserve, there is no winner.
--
--   A winner $i$ pays
--   $$\max\{r,\max_{j\ne i} b_j\},$$
--   where absent competing bids contribute zero. Every loser pays zero, and no sale generates no payment. Below-reserve competing bids cannot affect this maximum. The definition gives each possible winner's exact probability, as well as the realized price and individual payments.
--
--   This auction is defined for arbitrary submitted bids and is reused both downstream and upstream. **Formalization Note** Bidders are indexed by $\mathrm{Fin}\,n$. An absent bid has its own measurable point in a disjoint sum; it is distinct from a submitted zero bid, which meets a zero reserve. The zero-bidder and no-eligible-bid cases explicitly give no sale with probability one.
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 7 (PDF 8), §2; p. 9 (PDF 10), Definition 3.1; p. 13 (PDF 14), §5.2.1

import Mathlib

open MeasureTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

/-- The disjoint-sum measurable structure: an absent bid is an isolated point. -/
instance optionMeasurableSpace {α : Type*} [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap (fun q : Option α => match q with
    | none => (Sum.inr () : α ⊕ Unit) | some a => Sum.inl a) inferInstance

/-- A general single-item second-price auction: absence is distinct from a bid of zero. -/
def Meets (r : ℝ≥0) (b : Option ℝ≥0) : Prop := ∃ x, b = some x ∧ r ≤ x

noncomputable def topBidders {n : ℕ} (r : ℝ≥0) (b : Fin n → Option ℝ≥0) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => Meets r (b i) ∧
    ∀ j, Meets r (b j) → (b j).getD 0 ≤ (b i).getD 0

/-- The exact uniform probability of each possible winner, including no sale. -/
noncomputable def spaWeight {n : ℕ} (r : ℝ≥0) (b : Fin n → Option ℝ≥0)
    (w : Option (Fin n)) : ℝ≥0∞ := by
  classical
  exact match w with
    | none => if topBidders r b = ∅ then 1 else 0
    | some i => if i ∈ topBidders r b then ((topBidders r b).card : ℝ≥0∞)⁻¹ else 0

/-- The winner pays the reserve or the largest competing bid, whichever is greater.
Bids below the reserve cannot change this maximum; an empty competitor set contributes zero. -/
noncomputable def spaPrice {n : ℕ} (r : ℝ≥0) (b : Fin n → Option ℝ≥0)
    (w : Option (Fin n)) : ℝ≥0 := by
  classical
  exact match w with
    | none => 0
    | some i => max r ((Finset.univ.erase i).sup fun j => (b j).getD 0)

noncomputable def spaPayment {n : ℕ} (r : ℝ≥0) (b : Fin n → Option ℝ≥0)
    (w : Option (Fin n)) (i : Fin n) : ℝ≥0 := by
  classical
  exact if w = some i then spaPrice r b w else 0

end MultiInterm.Compete


