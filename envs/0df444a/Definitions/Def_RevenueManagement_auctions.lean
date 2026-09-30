-- Prove2me | Definitions.Def_RevenueManagement_auctions
-- name    : RevenueManagement_auctions
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T00:51:28.067978+00:00
-- url     : https://prove2.me/theorems/26bef62f-b3eb-434d-9d6d-0abb0ce86e30
-- title:
--   Auctions, Chapter 6: the independent private-value model, direct-revelation mechanisms, incentive compatibility, virtual values, and the second-price, list-price and first-price mechanisms
-- statement:
--   The independent private-value auction model of Sect. 6.2 of Talluri and van Ryzin.
--
--   **Valuations.** `PrivateValues` carries $N$ customers, an upper bound $\bar v$, a
--   distribution $F$ and its density $f$; `IsRegular` says $F$ is continuously
--   differentiable with derivative $f$ on $[0, \bar v]$, $f$ is continuous and positive there,
--   $F(0) = 0$ and $F(\bar v) = 1$. `μ` is the law of one valuation (density $f$ on
--   $[0, \bar v]$) and `joint` the product law of the $N$ i.i.d. valuations. The **virtual
--   value** is $J(v) = v - (1 - F(v))/f(v)$ (`virtualValue`), the marginal revenue of (7.14).
--
--   **Mechanisms.** A direct-revelation mechanism (`Mechanism N`) is an allocation rule
--   $y_i(v) \in \{0, 1\}$ and a payment rule $p_i(v)$ on reported valuation vectors;
--   `IsFeasible C vbar` says allocations are in $\{0,1\}$ with at most $C$ units awarded, the
--   rules are measurable and payments are bounded on reports in $[0, \bar v]^N$. For a report $w$ by customer $i$ with the others
--   reporting their valuations, $P_i(w)$ is the win probability (`winProb`), $R_i(w)$ the
--   expected payment (`expPayment`), $S_i(w) = w P_i(w) - R_i(w)$ the expected surplus of a
--   truthful customer (`expSurplus`), and $\mathbb E[\sum_i p_i(v)]$ the firm's expected
--   revenue (`expRevenue`). `IsIncentiveCompatible` is the equilibrium condition of Sect.
--   6.2.3.1, $S_i(w) \ge w P_i(w') - R_i(w')$ for all $w, w' \in [0, \bar v]$;
--   `HasMonotoneAllocation` is condition (i) of Theorem 6.1, $y_i(v_i, v_{-i})$ increasing in
--   $v_i$; `HasZeroSurplusAtZero` is condition (ii), $S_i(0) = 0$.
--
--   **The mechanisms of the chapter.** `secondPriceReserve N C r` is the standard $C$-unit
--   second-price auction with reserve price $r$: the $C$ highest valuations above $r$ win
--   (ties broken by index) and each winner pays $\max\{r, \text{the highest losing valuation}\}$,
--   $r$ if there is no loser. `listPrice N price` is the list-price mechanism for the case
--   where every willing customer can be served: a customer with valuation above the price gets
--   a unit and pays the price. For the single-unit first-price auction, `firstPriceWinProb` is
--   $P(v) = F(v)^{N-1}$ of (6.1) and `firstPriceBid` the symmetric equilibrium bid
--   $b^*(v) = v - \int_0^v P(s)\,ds / P(v)$ of (6.4). `spSurplus v b others` is the surplus of a
--   customer with valuation $v$ bidding $b$ in a single-unit second-price auction: the strictly
--   highest bid wins and pays the highest other bid.
--
--   **Formalization Note** Expectations over the other customers' valuations are integrals
--   over the joint law with customer $i$'s coordinate overwritten by the report, which equals
--   the expectation over $v_{-i}$ since the law is a product. Ties in the second-price auction
--   are broken by index, a null event under a density; the reserve-price auction's payment uses
--   a supremum over the losers, which is $0$ when all customers win so that the winner pays
--   $r$. In (6.4) the quotient is Lean's, so $b^*(0) = 0$, the boundary condition of Appendix
--   6.A. Payments are assumed bounded on reports in $[0, \bar v]^N$, where the joint law lives,
--   so that expected payments are integrals of integrable functions. The bound is not asked on
--   all of $\mathbb R^N$: there the second-price auction's payment, the highest losing report, is
--   unbounded, and the goal's feasibility claim would be false.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, Sect. 6.2.1 pp. 247-248, Sect. 6.2.2 pp. 248-253 (Eq. 6.1-6.4), Sect. 6.2.3 pp. 254-256 (Eq. 6.5, incentive compatibility), Sect. 6.2.4-6.2.6 pp. 257-263 (Eq. 6.6-6.8, Eq. 6.10)

import Mathlib

open MeasureTheory

namespace RevenueManagement

/-! ### Auctions, Chapter 6 of Talluri and van Ryzin: the independent private-value model -/

/-- The independent private-value model of Sect. 6.2.1: `N` customers with i.i.d. valuations on
`[0, vbar]`, distribution `F` with density `f`. -/
structure PrivateValues where
  N : ℕ
  vbar : ℝ
  F : ℝ → ℝ
  f : ℝ → ℝ

/-- Regularity of the valuation distribution: `F` is continuously differentiable with derivative
`f` on `[0, vbar]`, `f` continuous and positive there, `F 0 = 0` and `F vbar = 1`. -/
def PrivateValues.IsRegular (V : PrivateValues) : Prop :=
  0 < V.vbar ∧ V.F 0 = 0 ∧ V.F V.vbar = 1 ∧ ContinuousOn V.f (Set.Icc 0 V.vbar) ∧
    (∀ v ∈ Set.Icc 0 V.vbar, 0 < V.f v) ∧
    ∀ v ∈ Set.Icc 0 V.vbar, HasDerivWithinAt V.F (V.f v) (Set.Icc 0 V.vbar) v

/-- The distribution of one valuation: the measure with density `f` on `[0, vbar]`. -/
noncomputable def PrivateValues.μ (V : PrivateValues) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 V.vbar)).withDensity (fun v => ENNReal.ofReal (V.f v))

/-- The joint distribution of the `N` i.i.d. valuations. -/
noncomputable def PrivateValues.joint (V : PrivateValues) : Measure (Fin V.N → ℝ) :=
  Measure.pi (fun _ => V.μ)

/-- The virtual value `J(v) = v − (1 − F(v)) / f(v)` of Theorem 6.1, the marginal revenue (7.14). -/
noncomputable def virtualValue (V : PrivateValues) (v : ℝ) : ℝ := v - (1 - V.F v) / V.f v

/-- A direct-revelation mechanism (Sect. 6.2.3.1): an allocation `y v i ∈ {0, 1}` and a payment
`p v i` of each customer `i` as functions of the reported valuations `v`. -/
structure Mechanism (N : ℕ) where
  y : (Fin N → ℝ) → Fin N → ℝ
  p : (Fin N → ℝ) → Fin N → ℝ

/-- A `C`-unit mechanism on valuations in `[0, vbar]`: allocations in `{0, 1}` with at most
`C` units awarded, measurable allocation and payment rules, and payments bounded on reports
in `[0, vbar]^N`. (Only there: the second-price auction's payment is the highest losing
report, which is unbounded over all of `ℝ^N`.) -/
def Mechanism.IsFeasible {N : ℕ} (M : Mechanism N) (C : ℕ) (vbar : ℝ) : Prop :=
  (∀ v i, M.y v i = 0 ∨ M.y v i = 1) ∧ (∀ v, ∑ i, M.y v i ≤ C) ∧
    (∀ i, Measurable (fun v => M.y v i)) ∧ (∀ i, Measurable (fun v => M.p v i)) ∧
    ∃ K, ∀ v, (∀ j, v j ∈ Set.Icc 0 vbar) → ∀ i, |M.p v i| ≤ K

/-- `P_i(w)`: the probability that customer `i` is awarded a unit when reporting `w` and the
others report their valuations. -/
noncomputable def winProb (V : PrivateValues) (M : Mechanism V.N) (i : Fin V.N) (w : ℝ) : ℝ :=
  ∫ v, M.y (Function.update v i w) i ∂V.joint

/-- `R_i(w)`: the expected payment of customer `i` when reporting `w`. -/
noncomputable def expPayment (V : PrivateValues) (M : Mechanism V.N) (i : Fin V.N) (w : ℝ) : ℝ :=
  ∫ v, M.p (Function.update v i w) i ∂V.joint

/-- `S_i(w) = w P_i(w) − R_i(w)`: the expected surplus of a customer with valuation `w` who
reports it. -/
noncomputable def expSurplus (V : PrivateValues) (M : Mechanism V.N) (i : Fin V.N) (w : ℝ) : ℝ :=
  w * winProb V M i w - expPayment V M i w

/-- The firm's expected revenue `E[∑ᵢ p_i(v)]`. -/
noncomputable def expRevenue (V : PrivateValues) (M : Mechanism V.N) : ℝ :=
  ∫ v, ∑ i, M.p v i ∂V.joint

/-- Incentive compatibility (Sect. 6.2.3.1): reporting the true valuation `w` is no worse than
reporting any `w'`, `S_i(w) ≥ w P_i(w') − R_i(w')`. -/
def IsIncentiveCompatible (V : PrivateValues) (M : Mechanism V.N) : Prop :=
  ∀ i, ∀ w ∈ Set.Icc 0 V.vbar, ∀ w' ∈ Set.Icc 0 V.vbar,
    w * winProb V M i w' - expPayment V M i w' ≤ expSurplus V M i w

/-- Condition (i) of Theorem 6.1: each allocation `y_i(v_i, v_{-i})` is increasing in `v_i`. -/
def HasMonotoneAllocation (V : PrivateValues) (M : Mechanism V.N) : Prop :=
  ∀ i v, MonotoneOn (fun w => M.y (Function.update v i w) i) (Set.Icc 0 V.vbar)

/-- Condition (ii) of Theorem 6.1: customers with valuation zero have zero expected surplus. -/
def HasZeroSurplusAtZero (V : PrivateValues) (M : Mechanism V.N) : Prop :=
  ∀ i, expSurplus V M i 0 = 0

open Classical in
/-- Customer `i` wins in the `C`-unit second-price auction with reserve price `r`: its valuation
exceeds `r` and fewer than `C` customers are ahead of it (a higher valuation, or an equal one
with a smaller index). -/
def spWins (N C : ℕ) (r : ℝ) (v : Fin N → ℝ) (i : Fin N) : Prop :=
  r < v i ∧ (Finset.univ.filter (fun j => v i < v j ∨ (v j = v i ∧ j < i))).card < C

open Classical in
/-- The standard `C`-unit second-price auction with reserve price `r` as a direct mechanism: the
`C` highest valuations above `r` win and each winner pays the larger of `r` and the highest
losing valuation (the `(C+1)`-st highest), `r` when there is no loser. -/
noncomputable def secondPriceReserve (N C : ℕ) (r : ℝ) : Mechanism N where
  y v i := if spWins N C r v i then 1 else 0
  p v i := if spWins N C r v i then
    max r (sSup (Set.range fun j : {j // ¬ spWins N C r v j} => v j)) else 0

open Classical in
/-- The list-price mechanism at price `price` when every willing customer can be served: a
customer with valuation above the price receives a unit and pays the price. -/
noncomputable def listPrice (N : ℕ) (price : ℝ) : Mechanism N where
  y v i := if price < v i then 1 else 0
  p v i := if price < v i then price else 0

/-- `P(v) = F(v)^{N−1}` of (6.1): the probability of winning the single-unit first-price auction
with valuation `v` under a symmetric increasing strategy. -/
noncomputable def firstPriceWinProb (V : PrivateValues) (v : ℝ) : ℝ := V.F v ^ (V.N - 1)

/-- The symmetric equilibrium bid of the first-price auction, Eq. (6.4):
`b*(v) = v − (∫₀ᵛ P(s) ds) / P(v)` (and `b*(0) = 0`). -/
noncomputable def firstPriceBid (V : PrivateValues) (v : ℝ) : ℝ :=
  v - (∫ s in (0 : ℝ)..v, firstPriceWinProb V s) / firstPriceWinProb V v

open Classical in
/-- The surplus of a customer with valuation `v` who bids `b` in a single-unit second-price
auction against the bids `others`: the item goes to the strictly highest bid, at the price of the
highest other bid. -/
noncomputable def spSurplus {m : ℕ} (v b : ℝ) (others : Fin m → ℝ) : ℝ :=
  if ∀ j, others j < b then v - sSup (Set.range others) else 0

end RevenueManagement


