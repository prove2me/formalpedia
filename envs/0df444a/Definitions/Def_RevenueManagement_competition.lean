-- Prove2me | Definitions.Def_RevenueManagement_competition
-- name    : RevenueManagement_competition
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T01:02:23.474137+00:00
-- url     : https://prove2.me/theorems/6b96100f-9422-48cc-8da0-9a85523ed61e
-- title:
--   Competition, Chapter 8: the equilibrium graph, the RM duopoly, the duopoly newsvendor, linear Cournot, Bertrand-Edgeworth with efficient rationing, advance purchases, and MNL offer-set competition
-- statement:
--   The competitive models of Chapter 8 of Talluri and van Ryzin that the book itself analyzes.
--
--   **Games on chains and the equilibrium graph** (Sect. 8.4.1.3). A two-firm game with
--   strategies `Fin m`, `Fin n` and payoffs $u_1, u_2$; `IsBestResponse1 u1 j i` says $i$ is a
--   best response of firm 1 to $j$, `IsNashEquilibrium` a pure Nash equilibrium. The
--   **equilibrium graph** has an arc $(j, i)$ for each best response; it has **no crossing arcs**
--   for firm 1 (`NoCrossing1`) when arcs $(k_2, k_1)$, $(l_2, l_1)$ with $k_2 < l_2$ always have
--   $k_1 \le l_1$, and `ReverseCrossing1` is the mirror condition $l_1 \le k_1$.
--
--   **The RM duopoly** (Sect. 8.4.1.3). Two firms with capacity $C$ sell a low fare $p_L$ and a
--   high fare $p_H$; a firm's effective high-fare demand when its rival protects $y'$ units is
--   its own demand plus the rival's excess, `spilloverDemand D D' y' = D + (D' − y')⁺$; and
--   `littlewoodResponse P R pL pH C` is Littlewood's protection level, the largest $y \le C$
--   with $p_L < p_H\, \mathbb P(R \ge y)$.
--
--   **The duopoly newsvendor** (Example 8.16): `effectiveDemand D D' x'` is
--   $R_1(x) = D_1 + (D_2 - x_2)^+$. **Linear Cournot** (Example 8.15): `cournotPayoff a c x i`
--   is $x_i(a - \sum_j x_j) - c x_i$. **Bertrand–Edgeworth with efficient rationing** (Sect.
--   8.4.1.5): with demand $d(p) = a - p$ and capacity $C$ per firm, `beSales a C p i` is firm
--   $i$'s sales, the residual demand after the firms priced below it have served the
--   highest-valuation customers, shared equally among firms at the same price and capped at
--   $C$; `bePayoff` is $(p_i - c)$ times sales and `IsBEEquilibrium` a pure Nash equilibrium in
--   prices. **Advance purchases** (Sect. 8.3.6): `peakLoadRevenue` is
--   $V_{peak}(w) = vC + (v - w)((1-\alpha) + \alpha F(w))$ and `advancePurchaseRevenue` is
--   (8.14). **Offer-set competition** (Sect. 8.4.3.2): an `OfferFirm` has $n$ products with MNL
--   weights $w_j > 0$ and decreasing prices $p_j$ and the value differences $\Delta, \delta$ of
--   (8.31); `g` is $g(C_k) = \sum_{j \in C_k} w_j(p_j - \Delta) - w_0\delta$, `offerPayoff1 A B w0 k l`
--   is $g_1(C_k)/(W_1(k) + W_2(l) + w_0)$ (firm 2 symmetric), `CaseI` says $g(G^*) \ge 0$, `CaseII`
--   that every complete set has $g < 0$, and `IsOfferEquilibrium` is a pure equilibrium in
--   complete sets $(C_k, C_l)$, $1 \le k \le n_1$, $1 \le l \le n_2$.
--
--   **Formalization Note** Products are indexed from $0$ and the complete set $C_k$ is the first
--   $k$ products, $k \ge 1$ as in the book's strategy spaces. The one-period objective (8.31)
--   is taken up to the positive factor $\lambda$ and the terms that depend on neither firm's
--   offer set. Sales under efficient rationing are defined by recursion over the firms priced
--   strictly below a given firm. The book's chains are indexed by $j$ (firm 2 protects $C - j$
--   units), so its "no crossing" is the monotonicity of best responses in the rival's index.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, Sect. 8.3.6 pp. 372-374 (Eq. 8.13-8.15), Sect. 8.4.1.1 pp. 376-377 (Eq. 8.16-8.20), Sect. 8.4.1.2 pp. 378-380 (Eq. 8.22-8.23), Sect. 8.4.1.3 pp. 380-381 (the equilibrium graph), Sect. 8.4.1.5 pp. 385-386, Sect. 8.4.3.2 pp. 396-399 (Eq. 8.30-8.31)

import Mathlib

open MeasureTheory

namespace RevenueManagement

/-! ### Competition, Chapter 8 of Talluri and van Ryzin -/

/-! #### Two-firm games on finite chains and the equilibrium graph, Sect. 8.4.1.3 -/

/-- `i` is a best response of firm 1 to firm 2's strategy `j` in the game with payoff `u1`. -/
def IsBestResponse1 {m n : ℕ} (u1 : Fin m → Fin n → ℝ) (j : Fin n) (i : Fin m) : Prop :=
  ∀ i', u1 i' j ≤ u1 i j

/-- `j` is a best response of firm 2 to firm 1's strategy `i` in the game with payoff `u2`. -/
def IsBestResponse2 {m n : ℕ} (u2 : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : Prop :=
  ∀ j', u2 i j' ≤ u2 i j

/-- A pure-strategy Nash equilibrium of the two-firm game with payoffs `u1`, `u2`. -/
def IsNashEquilibrium {m n : ℕ} (u1 u2 : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : Prop :=
  IsBestResponse1 u1 j i ∧ IsBestResponse2 u2 i j

/-- The equilibrium graph of firm 1 has no crossing arcs (Proposition 8.1): best-response arcs
`(k2, k1)` and `(l2, l1)` with `k2 < l2` never have `l1 < k1`. -/
def NoCrossing1 {m n : ℕ} (u1 : Fin m → Fin n → ℝ) : Prop :=
  ∀ k2 l2 k1 l1, k2 < l2 → IsBestResponse1 u1 k2 k1 → IsBestResponse1 u1 l2 l1 → k1 ≤ l1

/-- Firm 2's equilibrium graph has no crossing arcs. -/
def NoCrossing2 {m n : ℕ} (u2 : Fin m → Fin n → ℝ) : Prop :=
  ∀ k1 l1 k2 l2, k1 < l1 → IsBestResponse2 u2 k1 k2 → IsBestResponse2 u2 l1 l2 → k2 ≤ l2

/-- The reverse condition for firm 1: best responses are nonincreasing in the rival's strategy. -/
def ReverseCrossing1 {m n : ℕ} (u1 : Fin m → Fin n → ℝ) : Prop :=
  ∀ k2 l2 k1 l1, k2 < l2 → IsBestResponse1 u1 k2 k1 → IsBestResponse1 u1 l2 l1 → l1 ≤ k1

/-- The reverse condition for firm 2. -/
def ReverseCrossing2 {m n : ℕ} (u2 : Fin m → Fin n → ℝ) : Prop :=
  ∀ k1 l1 k2 l2, k1 < l1 → IsBestResponse2 u2 k1 k2 → IsBestResponse2 u2 l1 l2 → l2 ≤ k2

/-! #### The RM duopoly game with Littlewood best responses, Sect. 8.4.1.3 -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The effective high-fare demand of a firm when its rival protects `y'` units: its own high-fare
demand plus the rival's high-fare demand in excess of the rival's protection level. -/
def spilloverDemand (D D' : Ω → ℕ) (y' : ℕ) (ω : Ω) : ℕ := D ω + (D' ω - y')

open Classical in
/-- Littlewood's protection level for the high fare `pH` against the low fare `pL` when the
high-fare demand is `R`: the largest `y ≤ C` with `pL < pH P(R ≥ y)`, and `0` when there is none. -/
noncomputable def littlewoodResponse (P : Measure Ω) (R : Ω → ℕ) (pL pH : ℝ) (C : ℕ) : ℕ :=
  ((Finset.range (C + 1)).filter (fun y => 1 ≤ y ∧ pL < pH * (P {ω | y ≤ R ω}).toReal)).sup id

/-! #### The duopoly newsvendor game, Sect. 8.4.1.2, Example 8.16 -/

/-- The effective demand `R_1(x) = D_1 + (D_2 − x_2)⁺` of firm 1 in the duopoly newsvendor game
(customers whose preferred firm is sold out switch to the other firm). -/
def effectiveDemand (D D' : Ω → ℝ) (x' : ℝ) (ω : Ω) : ℝ := D ω + max (D' ω - x') 0

/-! #### Cournot competition with linear demand, Example 8.15 -/

/-- Firm `i`'s Cournot payoff `x_i (a − X) − c x_i` with linear inverse demand `p(X) = a − X`. -/
def cournotPayoff {n : ℕ} (a c : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i * (a - ∑ j, x j) - c * x i

/-! #### Bertrand–Edgeworth competition with efficient rationing, Sect. 8.4.1.5 -/

open Classical in
/-- The sales of firm `i` at prices `p` under the efficient-rationing rule with linear demand
`d(p) = a − p` and capacity `C` per firm: lower-priced firms serve the highest-valuation
customers first, so firm `i` faces the residual demand `max {0, d(p_i) − (sales of the firms
priced below p_i)}`, shared equally among the firms priced at `p_i`, and sells at most `C`. -/
noncomputable def beSales {n : ℕ} (a C : ℝ) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  min C (max 0 (a - p i -
    ∑ j ∈ (Finset.univ.filter (fun j => p j < p i)).attach, beSales a C p j.1) /
      ((Finset.univ.filter (fun j => p j = p i)).card : ℝ))
termination_by (Finset.univ.filter (fun j => p j < p i)).card
decreasing_by
  have hj : p j.1 < p i := (Finset.mem_filter.1 j.2).2
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans hj
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
    simp at this

/-- Firm `i`'s profit `(p_i − c) × sales` in the Bertrand–Edgeworth game. -/
noncomputable def bePayoff {n : ℕ} (a c C : ℝ) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  (p i - c) * beSales a C p i

/-- A pure-strategy Nash equilibrium in prices of the Bertrand–Edgeworth game. -/
def IsBEEquilibrium {n : ℕ} (a c C : ℝ) (p : Fin n → ℝ) : Prop :=
  ∀ i (p' : ℝ), bePayoff a c C (Function.update p i p') i ≤ bePayoff a c C p i

/-! #### Advance purchases versus peak-load pricing, Sect. 8.3.6 -/

/-- The peak-load revenue `V_peak(w) = vC + (v − w)((1 − α) + αF(w))` of the monopolist charging
`v` on the peak flight and `v − w` on the off-peak flight. -/
noncomputable def peakLoadRevenue (v C α : ℝ) (F : ℝ → ℝ) (w : ℝ) : ℝ :=
  v * C + (v - w) * ((1 - α) + α * F w)

/-- The advance-purchase-discount revenue (8.14),
`V_APD(w) = v(C + (1 − α)(1 − F(w))) + (v − αw)F(w)`. -/
noncomputable def advancePurchaseRevenue (v C α : ℝ) (F : ℝ → ℝ) (w : ℝ) : ℝ :=
  v * (C + (1 - α) * (1 - F w)) + (v - α * w) * F w

/-! #### Offer-set competition under the MNL choice model, Sect. 8.4.3.2 -/

/-- A firm in the offer-set game: `n` fare products indexed `0, …, n − 1` (the book's `1, …, n`)
with MNL weights `w j > 0` and prices `p j` decreasing in `j`, and the value differences `Δ`, `δ`
of (8.31) from the equilibrium revenue to go. -/
structure OfferFirm where
  n : ℕ
  w : ℕ → ℝ
  p : ℕ → ℝ
  Δ : ℝ
  δ : ℝ

/-- The model assumptions: at least one product, positive weights, prices decreasing in the
product index (the nested-by-revenue order). -/
def OfferFirm.IsModel (A : OfferFirm) : Prop := 1 ≤ A.n ∧ (∀ j, 0 < A.w j) ∧ Antitone A.p

/-- The total weight `∑_{j < k} w_j` of the complete set `C_k` of the first `k` products. -/
def OfferFirm.weight (A : OfferFirm) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, A.w j

/-- `g(C_k) = ∑_{j ∈ C_k} w_j (p_j − Δ) − w_0 δ`, the numerator of the firm's one-period objective. -/
def OfferFirm.g (A : OfferFirm) (w0 : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, A.w j * (A.p j - A.Δ) - w0 * A.δ

/-- Firm 1's one-period objective (8.31) when it offers `C_k` and firm 2 offers `C_l`:
`g_1(C_k) / (W_1(k) + W_2(l) + w_0)`, the MNL denominator including the no-purchase weight. -/
noncomputable def offerPayoff1 (A B : OfferFirm) (w0 : ℝ) (k l : ℕ) : ℝ :=
  A.g w0 k / (A.weight k + B.weight l + w0)

/-- Firm 2's one-period objective when firm 1 offers `C_k` and it offers `C_l`. -/
noncomputable def offerPayoff2 (A B : OfferFirm) (w0 : ℝ) (k l : ℕ) : ℝ :=
  B.g w0 l / (A.weight k + B.weight l + w0)

/-- Case I of Sect. 8.4.3.2: the set `G*` maximizing `g` has `g(G*) ≥ 0` (p. 399; the boundary
`g(G*) = 0` is Case I, so Cases I and II cover every firm). -/
def OfferFirm.CaseI (A : OfferFirm) (w0 : ℝ) : Prop := ∃ k ∈ Finset.Icc 1 A.n, 0 ≤ A.g w0 k

/-- Case II: `g(G*) < 0`, every complete set has negative `g`. -/
def OfferFirm.CaseII (A : OfferFirm) (w0 : ℝ) : Prop := ∀ k ∈ Finset.Icc 1 A.n, A.g w0 k < 0

/-- A pure-strategy Nash equilibrium in complete offer sets `(C_k, C_l)`. -/
def IsOfferEquilibrium (A B : OfferFirm) (w0 : ℝ) (k l : ℕ) : Prop :=
  k ∈ Finset.Icc 1 A.n ∧ l ∈ Finset.Icc 1 B.n ∧
    (∀ k' ∈ Finset.Icc 1 A.n, offerPayoff1 A B w0 k' l ≤ offerPayoff1 A B w0 k l) ∧
    (∀ l' ∈ Finset.Icc 1 B.n, offerPayoff2 A B w0 k l' ≤ offerPayoff2 A B w0 k l)

end RevenueManagement


