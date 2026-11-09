-- Prove2me | Definitions.Def_MatchingGFT_TightE_OneSided
-- name    : MatchingGFT_TightE_OneSided
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:49.549108+00:00
-- url     : https://prove2.me/theorems/12bc1cd4-76ab-40bd-80e2-97e573beaa4b
-- title:
--   One-sided auction families and the benchmarks OPT^S, OPT^B
-- statement:
--   Jointly measurable families of feasible one-sided auctions indexed by the parameter side, a randomized allocation being a lottery over $\mathcal F$ with expected payments. BIC and interim IR hold at every nonnegative parameter vector. $\mathrm{OPT}^S$, $\mathrm{OPT}^B$ are extended-real suprema of $E[\pi^S]$, $E[\pi^B]$.
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), §2.2, PDF pp. 9–10

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market

open MeasureTheory

namespace MatchingGFT.TightE

variable {B S : Type*}

/-- A family of (possibly randomized) one-sided auctions indexed by the parameter side (PDF pp. 9–10).
A randomized allocation is encoded by a lottery over allocations; `pay` holds the expected
payment given the reports, which is all that BIC, interim IR and the objective use. For a buyer
auction `pay` is charged to the buyers (index `A = B`); for a procurement auction it is paid to
the sellers (index `A = S`). -/
structure AuctionFamily (B S A : Type*) where
  lottery : Profile B S → Finset (B × S) → ℝ
  pay : Profile B S → A → ℝ

/-- The lottery of an auction family is a jointly measurable probability on `ℱ`. -/
def AuctionFamily.IsFeasibleLottery {A : Type*} (m : Market B S) (a : AuctionFamily B S A) : Prop :=
  (∀ t M, 0 ≤ a.lottery t M) ∧ (∀ t, ∑ M ∈ m.family, a.lottery t M = 1) ∧
    (∀ t, ∀ M ∉ m.family, a.lottery t M = 0) ∧ ∀ M, Measurable fun t => a.lottery t M

/-- Probability that buyer `i` trades given the reports. -/
noncomputable def buyerAllocProb {A : Type*} (m : Market B S) (a : AuctionFamily B S A)
    (t : Profile B S) (i : B) : ℝ := by
  classical
  exact ∑ M ∈ m.family with buyerMatched M i, a.lottery t M

/-- Probability that seller `j` trades given the reports. -/
noncomputable def sellerAllocProb {A : Type*} (m : Market B S) (a : AuctionFamily B S A)
    (t : Profile B S) (j : S) : ℝ := by
  classical
  exact ∑ M ∈ m.family with sellerMatched M j, a.lottery t M

/-- A buyer-auction family (PDF p. 9): feasible lottery, jointly measurable payments, with
finite expected payments, ex ante and for every fixed report of one buyer and every cost vector. -/
def IsBuyerAuctionFamily [Fintype B] [Fintype S] [DecidableEq B] (m : Market B S)
    (a : AuctionFamily B S B) : Prop :=
  a.IsFeasibleLottery m ∧ (∀ i, Measurable fun t => a.pay t i) ∧
    (∀ i, Integrable (fun t => a.pay t i) (typeMeasure m)) ∧
    ∀ (c : S → ℝ) (i : B) (x : ℝ),
      Integrable (fun v : B → ℝ => a.pay (Function.update v i x, c) i) (buyerMeasure m)

/-- A procurement-auction family (PDF p. 10), symmetrically. -/
def IsSellerAuctionFamily [Fintype B] [Fintype S] [DecidableEq S] (m : Market B S)
    (a : AuctionFamily B S S) : Prop :=
  a.IsFeasibleLottery m ∧ (∀ j, Measurable fun t => a.pay t j) ∧
    (∀ j, Integrable (fun t => a.pay t j) (typeMeasure m)) ∧
    ∀ (v : B → ℝ) (j : S) (x : ℝ),
      Integrable (fun c : S → ℝ => a.pay (v, Function.update c j x) j) (sellerMeasure m)

/-- Interim utility of buyer `i` with true value `x` reporting `x'`, the seller costs `c` fixed, the
other buyers truthful: an expectation over the other buyers' values and the internal randomization
(the integrand does not depend on `vᵢ`). -/
noncomputable def buyerInterimUtility [Fintype B] [DecidableEq B] (m : Market B S)
    (a : AuctionFamily B S B) (c : S → ℝ) (i : B) (x x' : ℝ) : ℝ :=
  ∫ v : B → ℝ, (x * buyerAllocProb m a (Function.update v i x', c) i -
    a.pay (Function.update v i x', c) i) ∂buyerMeasure m

/-- Interim utility of seller `j` with true cost `x` reporting `x'`, the buyer values `v` fixed. -/
noncomputable def sellerInterimUtility [Fintype S] [DecidableEq S] (m : Market B S)
    (a : AuctionFamily B S S) (v : B → ℝ) (j : S) (x x' : ℝ) : ℝ :=
  ∫ c : S → ℝ, (a.pay (v, Function.update c j x') j -
    x * sellerAllocProb m a (v, Function.update c j x') j) ∂sellerMeasure m

/-- BIC for the buyers at every nonnegative cost vector (PDF pp. 9–10). -/
def IsBICBuyers [Fintype B] [DecidableEq B] (m : Market B S) (a : AuctionFamily B S B) : Prop :=
  ∀ c : S → ℝ, (∀ j, 0 ≤ c j) → ∀ (i : B) (x x' : ℝ), 0 ≤ x → 0 ≤ x' →
    buyerInterimUtility m a c i x x' ≤ buyerInterimUtility m a c i x x

/-- Interim IR for the buyers at every nonnegative cost vector (PDF p. 10). -/
def IsInterimIRBuyers [Fintype B] [DecidableEq B] (m : Market B S) (a : AuctionFamily B S B) : Prop :=
  ∀ c : S → ℝ, (∀ j, 0 ≤ c j) → ∀ (i : B) (x : ℝ), 0 ≤ x → 0 ≤ buyerInterimUtility m a c i x x

/-- BIC for the sellers at every nonnegative value vector (PDF p. 10). -/
def IsBICSellers [Fintype S] [DecidableEq S] (m : Market B S) (a : AuctionFamily B S S) : Prop :=
  ∀ v : B → ℝ, (∀ i, 0 ≤ v i) → ∀ (j : S) (x x' : ℝ), 0 ≤ x → 0 ≤ x' →
    sellerInterimUtility m a v j x x' ≤ sellerInterimUtility m a v j x x

/-- Interim IR for the sellers at every nonnegative value vector (PDF p. 10). -/
def IsInterimIRSellers [Fintype S] [DecidableEq S] (m : Market B S) (a : AuctionFamily B S S) : Prop :=
  ∀ v : B → ℝ, (∀ i, 0 ≤ v i) → ∀ (j : S) (x : ℝ), 0 ≤ x → 0 ≤ sellerInterimUtility m a v j x x

/-- Expected GFT at `t` over the auction's internal randomization. -/
noncomputable def lotteryGFT {A : Type*} (m : Market B S) (a : AuctionFamily B S A)
    (t : Profile B S) : ℝ :=
  ∑ M ∈ m.family, a.lottery t M * gft M t

/-- `π^S` at `t`, in expectation over the internal randomization (PDF p. 9). -/
noncomputable def objectiveS [Fintype B] (m : Market B S) (a : AuctionFamily B S B)
    (t : Profile B S) : ℝ :=
  ∑ i, a.pay t i - ∑ M ∈ m.family, a.lottery t M * ∑ e ∈ M, t.2 e.2

/-- `π^B` at `t`, in expectation over the internal randomization (PDF p. 10). -/
noncomputable def objectiveB [Fintype S] (m : Market B S) (a : AuctionFamily B S S)
    (t : Profile B S) : ℝ :=
  ∑ M ∈ m.family, a.lottery t M * ∑ e ∈ M, t.1 e.1 - ∑ j, a.pay t j

/-- `OPT^S` (PDF p. 9): the supremum of `E[π^S]` over jointly measurable families of feasible buyer
auctions that are BIC and interim IR for the buyers. An extended-real supremum. -/
noncomputable def optS [Fintype B] [Fintype S] [DecidableEq B] (m : Market B S) : EReal :=
  ⨆ a : {a : AuctionFamily B S B //
      IsBuyerAuctionFamily m a ∧ IsBICBuyers m a ∧ IsInterimIRBuyers m a},
    ((∫ t, objectiveS m a.1 t ∂typeMeasure m : ℝ) : EReal)

/-- `OPT^B` (PDF p. 10): the supremum of `E[π^B]` over jointly measurable families of feasible
procurement auctions that are BIC and interim IR for the sellers. -/
noncomputable def optB [Fintype B] [Fintype S] [DecidableEq S] (m : Market B S) : EReal :=
  ⨆ a : {a : AuctionFamily B S S //
      IsSellerAuctionFamily m a ∧ IsBICSellers m a ∧ IsInterimIRSellers m a},
    ((∫ t, objectiveB m a.1 t ∂typeMeasure m : ℝ) : EReal)

end MatchingGFT.TightE


