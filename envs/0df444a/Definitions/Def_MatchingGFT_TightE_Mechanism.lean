-- Prove2me | Definitions.Def_MatchingGFT_TightE_Mechanism
-- name    : MatchingGFT_TightE_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:04.757822+00:00
-- url     : https://prove2.me/theorems/3993c061-d1aa-42c8-b24d-4d010d77f17c
-- title:
--   GSOM, GBOM, GRO, threshold payments and incentive properties
-- statement:
--   GSOM and GBOM select the tie-broken maximizers of $\sum(\phi_i(v_i)-c_j)$ and $\sum(v_i-\psi_j(c_j))$ with normalized threshold payments on each side. GRO runs one of them by a fair coin independent of the reports. DSIC, ex-post IR and ex-ante WBB are defined as on PDF p. 9 for coin-indexed families, a deterministic mechanism being a constant family. $\Pi^S$, $\Pi^B$ and the expected GFT are expectations under truthful reports.
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), §2.1–2.2, §3, PDF pp. 9–11, 15

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Quantile

open MeasureTheory

namespace MatchingGFT.TightE

variable {B S : Type*}

/-- A deterministic two-sided direct mechanism: allocation, buyer charges and seller payments as
functions of the report profile. -/
structure Mechanism (B S : Type*) where
  alloc : Profile B S → Finset (B × S)
  buyerPay : Profile B S → B → ℝ
  sellerPay : Profile B S → S → ℝ

/-- Normalized threshold payments for an allocation rule (PDF pp. 10–11): holding the other reports
fixed, a matched buyer pays the infimum nonnegative report at which she is matched, a matched
seller receives the supremum nonnegative report at which she is matched, and unmatched agents make
and receive zero payments. -/
noncomputable def thresholdMechanism [DecidableEq B] [DecidableEq S]
    (alloc : Profile B S → Finset (B × S)) : Mechanism B S := by
  classical
  exact
    { alloc := alloc
      buyerPay := fun t i =>
        if buyerMatched (alloc t) i then
          sInf {x : ℝ | 0 ≤ x ∧ buyerMatched (alloc (updateBuyer t i x)) i}
        else 0
      sellerPay := fun t j =>
        if sellerMatched (alloc t) j then
          sSup {x : ℝ | 0 ≤ x ∧ sellerMatched (alloc (updateSeller t j x)) j}
        else 0 }

/-- Seller-side virtual surplus `Σ_{(i,j) ∈ M} (φᵢ(vᵢ) - cⱼ)` (PDF p. 10). A term with `φᵢ = -∞` is
`-∞`; such a set scores below the empty matching. -/
noncomputable def sellerVirtualSurplus (m : Market B S) (t : Profile B S) (M : Finset (B × S)) :
    EReal :=
  ∑ e ∈ M, (virtualValue (m.buyerLaw e.1) (t.1 e.1) - ((t.2 e.2 : ℝ) : EReal))

/-- Buyer-side virtual surplus `Σ_{(i,j) ∈ M} (vᵢ - ψⱼ(cⱼ))` (PDF p. 10). A term with `ψⱼ = +∞` is
`-∞`; such a set scores below the empty matching. -/
noncomputable def buyerVirtualSurplus (m : Market B S) (t : Profile B S) (M : Finset (B × S)) :
    EReal :=
  ∑ e ∈ M, (((t.1 e.1 : ℝ) : EReal) - virtualCost (m.sellerLaw e.2) (t.2 e.2))

/-- GSOM (PDF pp. 10–11): the tie-broken maximizer of seller-side virtual surplus with normalized
threshold payments. -/
noncomputable def gsom [DecidableEq B] [DecidableEq S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) : Mechanism B S :=
  thresholdMechanism fun t => tieBrokenMax m rank (sellerVirtualSurplus m t)

/-- GBOM (PDF pp. 10–11): the tie-broken maximizer of buyer-side virtual surplus with normalized
threshold payments. -/
noncomputable def gbom [DecidableEq B] [DecidableEq S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) : Mechanism B S :=
  thresholdMechanism fun t => tieBrokenMax m rank (buyerVirtualSurplus m t)

/-- GRO `ℳ` (PDF p. 11): a fair coin independent of the reports picks GSOM (`true`) or GBOM
(`false`). A deterministic mechanism `A` is the constant family `fun _ => A`. -/
noncomputable def gro [DecidableEq B] [DecidableEq S] (m : Market B S)
    (rank : Finset (B × S) → ℕ) : Bool → Mechanism B S :=
  fun b => if b then gsom m rank else gbom m rank

/-- Expectation over the mechanism's fair coin. -/
noncomputable def coinAverage (f : Bool → ℝ) : ℝ := (1 / 2) * f true + (1 / 2) * f false

open Classical in
/-- Realized quasilinear utility of a buyer with true value `x` in the outcome at `t`. -/
noncomputable def buyerUtility (A : Mechanism B S) (t : Profile B S) (i : B) (x : ℝ) : ℝ :=
  (if buyerMatched (A.alloc t) i then x else 0) - A.buyerPay t i

open Classical in
/-- Realized quasilinear utility of a seller with true cost `x` in the outcome at `t`. -/
noncomputable def sellerUtility (A : Mechanism B S) (t : Profile B S) (j : S) (x : ℝ) : ℝ :=
  A.sellerPay t j - (if sellerMatched (A.alloc t) j then x else 0)

/-- DSIC (PDF p. 9): for every agent, true type, report and fixed nonnegative profile of the other
agents' reports, truthful reporting maximizes the utility averaged over the coin only. -/
def IsDSIC [DecidableEq B] [DecidableEq S] (A : Bool → Mechanism B S) : Prop :=
  (∀ (t : Profile B S), IsNonnegProfile t → ∀ (i : B) (x x' : ℝ), 0 ≤ x → 0 ≤ x' →
    coinAverage (fun b => buyerUtility (A b) (updateBuyer t i x') i x) ≤
      coinAverage (fun b => buyerUtility (A b) (updateBuyer t i x) i x)) ∧
  (∀ (t : Profile B S), IsNonnegProfile t → ∀ (j : S) (x x' : ℝ), 0 ≤ x → 0 ≤ x' →
    coinAverage (fun b => sellerUtility (A b) (updateSeller t j x') j x) ≤
      coinAverage (fun b => sellerUtility (A b) (updateSeller t j x) j x))

/-- Ex-post IR (PDF p. 9): every truthful agent has nonnegative utility for every nonnegative profile
of the other agents' reports and every realization of the coin. -/
def IsExPostIR [DecidableEq B] [DecidableEq S] (A : Bool → Mechanism B S) : Prop :=
  ∀ b : Bool,
    (∀ (t : Profile B S), IsNonnegProfile t → ∀ (i : B) (x : ℝ), 0 ≤ x →
      0 ≤ buyerUtility (A b) (updateBuyer t i x) i x) ∧
    (∀ (t : Profile B S), IsNonnegProfile t → ∀ (j : S) (x : ℝ), 0 ≤ x →
      0 ≤ sellerUtility (A b) (updateSeller t j x) j x)

/-- Ex-ante WBB (PDF p. 9): under truthful reporting, expected total buyer payments are finite and
at least the finite expected total seller payments, over the type profile and the coin. -/
def IsExAnteWBB [Fintype B] [Fintype S] (m : Market B S) (A : Bool → Mechanism B S) : Prop :=
  Integrable (fun t => coinAverage fun b => ∑ i, (A b).buyerPay t i) (typeMeasure m) ∧
  Integrable (fun t => coinAverage fun b => ∑ j, (A b).sellerPay t j) (typeMeasure m) ∧
  ∫ t, (coinAverage fun b => ∑ j, (A b).sellerPay t j) ∂typeMeasure m ≤
    ∫ t, (coinAverage fun b => ∑ i, (A b).buyerPay t i) ∂typeMeasure m

/-- `E[GFT(A)]` under truthful reports for a deterministic mechanism. -/
noncomputable def expectedGFT [Fintype B] [Fintype S] (m : Market B S) (A : Mechanism B S) : ℝ :=
  ∫ t, gft (A.alloc t) t ∂typeMeasure m

/-- `E[GFT(ℳ)] = ½ E[GFT(GSOM)] + ½ E[GFT(GBOM)]` (PDF p. 15). -/
noncomputable def groExpectedGFT [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (rank : Finset (B × S) → ℕ) : ℝ :=
  coinAverage fun b => expectedGFT m (gro m rank b)

/-- `Π^S(A) = E[π^S(A)]`, revenue from the buyers net of the seller costs of the trades
(PDF pp. 9–10). -/
noncomputable def profitS [Fintype B] [Fintype S] (m : Market B S) (A : Mechanism B S) : ℝ :=
  ∫ t, (∑ i, A.buyerPay t i - ∑ e ∈ A.alloc t, t.2 e.2) ∂typeMeasure m

/-- `Π^B(A) = E[π^B(A)]`, buyer value of the trades net of the seller payments (PDF p. 10). -/
noncomputable def profitB [Fintype B] [Fintype S] (m : Market B S) (A : Mechanism B S) : ℝ :=
  ∫ t, (∑ e ∈ A.alloc t, t.1 e.1 - ∑ j, A.sellerPay t j) ∂typeMeasure m

end MatchingGFT.TightE


