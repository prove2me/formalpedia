-- Prove2me | Definitions.Def_PostedPriceLimits_FullRevelation_Supplement_Analysis
-- name    : PostedPriceLimits_FullRevelation_Supplement_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:09:50.10449+00:00
-- url     : https://prove2.me/theorems/3da6d040-d8ec-4f12-ac64-5b56e0db1e1e
-- title:
--   The §4 empirical-price event, response-matrix event and welfare quantities
-- statement:
--   Fix a deterministic single-query mechanism visiting bidders in order $1,\ldots,n$ and the full §4 distribution. Two items are indistinguishable before visit $i$ when their coefficients agree in every earlier returned biased clause, including sample queries. An $i$-relevant slice has owner $j>i$ and all earlier role coordinates zero. An item is $i$-relevant if it belongs to such a slice or has owner $i$ and full role vector zero. Write $X_{i,K}$ for the relevant items with ranks in $K$, and $Z_{i,K}$ for the owner-$i$, full-zero-role items with ranks in $K$.
--
--   For nonempty $S$ and extended prices $p$, let
--
--   $$F(q,S,p)=\frac{|\{x\in S:p_x<q\}|}{|S|}.$$
--
--   The event $\mathcal E$ requires, at every actual visit and for every pair of nonempty unions of whole fibres $S,T$ whose union is indistinguishable before that visit, that $|F(q,S,p)-F(q,T,p)|\le\lambda^{-4}$ for all $q\ge0$, using the prices actually posted at that visit. It is computed from the transcript and hidden draw, rather than supplied as a concentration assumption.
--
--   The response-matrix event is exactly $\mathcal E$ together with both simultaneous conditions of Proposition 4.9: every $X_{i,K}$ for $K\in\mathcal K_{i-1}$ is indistinguishable, and whenever demand is nonempty there is one matrix $Q$ of depth at most $i-1$ used on every relevant slice by the returned clause list. The internal quantity of Definition 4.8 is $B_{i,k,r}=\int_{\operatorname{val}(r)-1}^{\operatorname{val}(r)}F(q,X_{i,\mathcal K_{i-1}(k)},p)\,dq$.
--
--   Set $S_i=\varnothing$ for a sample bidder and otherwise equal to its reported demand. The affordability and stealing fractions are
--
--   $$f_i(k)=F(\beta^{1/2}\operatorname{val}(k),Z_{i,k},p)\mathbf1\{i\text{ is not sample}\},\qquad g_{i,j}(k)=\frac{|S_i\cap Z_{j,k}|}{|Z_{i,k}|}.$$
--
--   The core rank cardinalities are positive and equal across owners. Infinity is unaffordable and the inequality is strict. The module also computes actual owner welfare without bias, the sum $\sum_i v_i(M\setminus Z_{i,[\kappa]})$ bounding all non-owner welfare including biases, total biased welfare, the scale $H=\beta^{1/2}\kappa^2\lambda^{11}$, loss $L_n=2+2\beta^{-1/4}+n/\lambda$, and the base-two function $\log_2\log_2 m$.
--
--   These are the events and quantities used by the three §4 supports and the quantitative certificate of Theorem 2.1.
--
--   **Formalization Note** The CDF is assigned zero on the empty set; the price event only tests nonempty sets. A universal inequality over thresholds expresses the CDF maximum bound without a real supremum default. Visit index `i.val` is the number of previous visits, so it represents the source index $i-1$. No approximation property is bundled into either event.
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Definitions 4.2–4.8, pp.9–11 (PDF 10–12); §4.4, p.13 (PDF 14); §4.5, pp.14–15 (PDF 15–16)

import Mathlib
import Definitions.Def_PostedPriceLimits_FullRevelation_Supplement_Instance

set_option autoImplicit false
open MeasureTheory
open ComplementFreeCA.XOSGreedy
open scoped ENNReal

namespace PostedPriceLimits.FullRevelation.Supplement

noncomputable section

def FixedOrder {n m : ℕ} (M : DetSQ n m) : Prop :=
  ∀ h, nextBidder M h = (Finset.univ.filter (fun j => j ∉ visited h)).min

def queryPrice {n : ℕ} (ω : Draw n) (M : DetSQ n (itemCount n)) (i : Fin n) : Item n → ℝ≥0∞ :=
  postedPrices M (history M (biasedOracle ω) i.val)

/-- Definition 4.2, including clauses returned by sample queries. -/
def Indistinguishable {n : ℕ} (ω : Draw n) (M : DetSQ n (itemCount n))
    (t : ℕ) (S : Finset (Item n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ r ∈ history M (biasedOracle ω) t, r.clause.2 x = r.clause.2 y

def relevantSlice {n : ℕ} (i : Fin n) (σ : Slice n i) : Prop :=
  i < σ.1.1 ∧ ∀ j : {j : Fin n // j ≠ i}, j.1 < i → roleInt (σ.2 j) = 0

def relevantLabel {n : ℕ} (i : Fin n) (L : Label n) : Prop :=
  (i < L.1 ∧ ∀ j : Fin n, j < i → roleInt (L.2.2.1 j) = 0) ∨
  (L.1 = i ∧ ∀ j, roleInt (L.2.2.1 j) = 0)

/-- Definition 4.3. -/
def X {n : ℕ} (ω : Draw n) (i : Fin n) (K : Finset ℕ) : Finset (Item n) := by
  classical
  exact Finset.univ.filter (fun x => relevantLabel i (labelAt ω x) ∧ (labelAt ω x).2.1.val + 1 ∈ K)

/-- Definition 4.4. -/
def Z {n : ℕ} (ω : Draw n) (i : Fin n) (K : Finset ℕ) : Finset (Item n) :=
  Finset.univ.filter (fun x => (labelAt ω x).1 = i ∧ (labelAt ω x).2.1.val + 1 ∈ K ∧
    ∀ j, roleInt ((labelAt ω x).2.2.1 j) = 0)

/-- Definition 4.5. Infinity never satisfies the strict inequality. At S=∅ use 0;
the event only tests nonempty sets. -/
def cdf {n : ℕ} (q : ℝ) (S : Finset (Item n)) (p : Item n → ℝ≥0∞) : ℝ :=
  ((S.filter (fun x => p x < ENNReal.ofReal q)).card : ℝ) / S.card

def WholeFibers {n : ℕ} (ω : Draw n) (S : Finset (Item n)) : Prop :=
  ∀ x y, labelAt ω x = labelAt ω y → (x ∈ S ↔ y ∈ S)

/-- Definition 4.6: all actual visits and all nonempty unions of complete fibers.
The universal threshold inequality is exactly the source's CDF maximum bound. -/
def priceEvent {n : ℕ} (M : DetSQ n (itemCount n)) : Set (Draw n) :=
  {ω | ∀ i : Fin n, ∀ S T : Finset (Item n), S.Nonempty → T.Nonempty →
    WholeFibers ω S → WholeFibers ω T → Indistinguishable ω M i.val (S ∪ T) →
    ∀ q : ℝ, 0 ≤ q → |cdf q S (queryPrice ω M i) - cdf q T (queryPrice ω M i)| ≤ (lam n : ℝ)⁻¹ ^ 4}

/-- Exactly E and both simultaneous conclusions of Proposition 4.9. The clause
index is internal: it is not part of the seller's history. -/
def matrixEvent {n : ℕ} (M : DetSQ n (itemCount n)) : Set (Draw n) :=
  {ω | ω ∈ priceEvent M ∧ ∀ i : Fin n,
    (∀ K ∈ rankPartition (kappa n) i.val, Indistinguishable ω M i.val (X ω i K)) ∧
    (demandSet (valuation ω i) (queryPrice ω M i) ≠ ∅ →
      ∃ Q : Matrix n, depth Q ≤ i.val ∧ ∀ σ : Slice n i, relevantSlice i σ →
        responseList ω i (queryPrice ω M i) σ = Q)}

/-- Definition 4.8, for internal proof work. -/
def B {n : ℕ} (ω : Draw n) (M : DetSQ n (itemCount n)) (i : Fin n) (k r : Rank n) : ℝ :=
  ∫ q in (value n (r.val + 1) - 1)..(value n (r.val + 1)),
    cdf q (X ω i (partOf (rankPartition (kappa n) i.val) (k.val + 1))) (queryPrice ω M i)

/-- The sample flag is fixed before the answer; samples have f_i=0. -/
def f {n : ℕ} (ω : Draw n) (M : DetSQ n (itemCount n)) (i : Fin n) (k : Rank n) : ℝ :=
  if M.sample (history M (biasedOracle ω) i.val) then 0
  else cdf (Real.sqrt (beta n) * value n (k.val + 1)) (Z ω i {k.val + 1}) (queryPrice ω M i)

def allocatedAt {n : ℕ} (ω : Draw n) (M : DetSQ n (itemCount n)) (i : Fin n) : Finset (Item n) :=
  if M.sample (history M (biasedOracle ω) i.val) then ∅
  else demandSet (valuation ω i) (queryPrice ω M i)

/-- Denominator is the current owner's core rank, as on the page. -/
def g {n : ℕ} (ω : Draw n) (M : DetSQ n (itemCount n)) (i j : Fin n) (k : Rank n) : ℝ :=
  (((allocatedAt ω M i) ∩ Z ω j {k.val + 1}).card : ℝ) / (Z ω i {k.val + 1}).card

def scale (n : ℕ) : ℝ := Real.sqrt (beta n) * (kappa n : ℝ)^2 * (lam n : ℝ)^11

def nonownerBoundValue {n : ℕ} (ω : Draw n) : ℝ :=
  ∑ i : Fin n, valuation ω i (Finset.univ \ Z ω i (rankRange (kappa n)))

/-- Actual owner welfare, with no bias. -/
def ownerWelfare {n : ℕ} (ω : Draw n) (M : DetSQ n (itemCount n)) : ℝ :=
  ∑ i : Fin n, ∑ x ∈ outcome M (biasedOracle ω) i ∩ Z ω i (rankRange (kappa n)),
    Real.sqrt (beta n) * value n ((labelAt ω x).2.1.val + 1)

def biasedWelfare {n : ℕ} (ω : Draw n) (M : DetSQ n (itemCount n)) : ℝ :=
  ∑ i : Fin n, valuation ω i (outcome M (biasedOracle ω) i)

/-- The sharper numeric certificate printed in §4.5. -/
def loss (n : ℕ) : ℝ := 2 + 2 * (beta n : ℝ) ^ (-(1 / 4 : ℝ)) + n / (lam n : ℝ)

def loglog (m : ℕ) : ℝ := Real.logb 2 (Real.logb 2 m)

end
end PostedPriceLimits.FullRevelation.Supplement


