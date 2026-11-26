-- Prove2me | Definitions.Def_MarketMakerAds_Supplement_HetMarket
-- name    : MarketMakerAds_Supplement_HetMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T21:33:04.362361+00:00
-- url     : https://prove2.me/theorems/71bf1831-d451-42bf-82cd-6f50470e87f4
-- title:
--   Market with heterogeneous risk aversion, its equilibria and the price $p^*_{M,k}$
-- statement:
--   A **market with heterogeneous risk aversion** extends the market of the base mission ($I$ identical units; in each outcome $\omega$ a random number $N(\omega)$ of units demanded with nonnegative values $V_0(\omega),\dots,V_{N(\omega)-1}(\omega)$, a buyer of demand $k_j$ being $k_j$ copies of its value) by
--
--   1. a number $k\ge1$ of **populations**;
--   2. a random **population label** $T_j(\omega)\in\{1,\dots,k\}$ of each unit, which may be correlated with the values;
--   3. one utility family (mean-variance or CARA) and parameters $\theta_1\le\theta_2\le\cdots\le\theta_k$ ($\beta_i\ge0$, resp. $\alpha_i>0$); population $k$ is the most risk-averse.
--
--   **Outcome at a clearing-price law $h$ and a Market-Maker price $p$.** A unit of value $v$ in population $i$ buys the contract when $p\le v$ and $U_A^{(i)}(v)\le U^{(i)}_{\mathrm{buy}}(v,p)$, its auction utility computed with $h$ (ties go to the Market-Maker). With $\ell$ contract units, the remaining units take part in an auction for the other $I-\ell$ units, with clearing price $c_1$ the $(I-\ell+1)$-th highest remaining value ($0$ if there are too few). The efficiency is the sum of the allocated values, the revenue is $R_1=\ell p+(I-\ell)c_1$, the buyers' utility sum $B_1$ gives $U_{\mathrm{buy}}$ to contract units and $U_A$ (under $h$) to the others, and the welfare is $W_1=B_1+R_1$. Without the contract, every unit gets $U_A^{(i)}(v)$ under the law $g$ of the clearing price $c$, and $W_0=B_0+R_0$.
--
--   **Equilibrium.** A law $h$ is an **equilibrium law at $p$** if $h$ is the law of the clearing price $c_1$ produced by the buyers' choices under $h$. A price $p$ is an **equilibrium Market-Maker price** if some equilibrium law at $p$ has at most $I$ contract units almost surely (the Market-Maker does not default) and at least one contract unit with positive probability.
--
--   **The price $p^*_{M,k}$** is the closed form (3) for the most risk-averse model, applied to $g$:
--   $$
--   p^*_{M,k}=\begin{cases}\mu_A+\beta_k\,\sigma_A^2&\text{(mean-variance)},\\ \tfrac1{\alpha_k}\log\mathbf E_g\big[e^{\alpha_k p}\big]&\text{(CARA)}.\end{cases}
--   $$
--
--   These objects are the setting of Theorem 4.
--
--   **Formalization Note** Labels are per unit and random, so the proportions $\rho_i$ of the paper are the law of the labels; fixed proportions are a special case. $I-\ell$ is truncated natural subtraction; it is used only where $\ell\le I$.
-- source:
--   Cohen, Désir, Korula, Sivan, Best of Both Worlds Ad Contracts, SSRN 3088600, §6, p.19 (populations); §3.1, p.10 (equilibrium as mutual best response); Remark 1, p.16 (default); p.20 (p*_{M,k}, eq. (3) with α = αk or β = βk); Appendix G, p.41

import Mathlib
import Definitions.Def_MarketMakerAds_Market
import Definitions.Def_MarketMakerAds_Supplement_RiskFamily

open MeasureTheory

namespace MarketMakerAds

namespace Supplement

/-- **A market with heterogeneous risk aversion** (§6).
Cohen, Désir, Korula, Sivan, *Best of Both Worlds Ad Contracts*, SSRN 3088600, §6, p.19: "We
assume that there are k populations of buyers with α1 ≤ α2 ≤ … ≤ αk (resp. β1 ≤ β2 ≤ … ≤ βk) for
CARA (resp. Mean-variance), where each population is present with proportion 0 ≤ ρi ≤ 1,
i = 1, …, k (Σ ρi = 1) among the N buyers."

The published market `Market` (`I` identical units, a random number `N ω` of units demanded with
nonnegative values `V ω j`) together with
* a number `k ≥ 1` of populations, indexed by `Fin k` (`0` is the paper's population 1, `k − 1` its
  population k);
* a random **population label** `T ω j` of each unit demanded;
* the model family `fam` and the parameters `θ i` (the paper's `α_i` or `β_i`), ordered
  `θ 0 ≤ θ 1 ≤ … ≤ θ (k − 1)`, each admissible: `β_i ≥ 0`, resp. `α_i > 0`.

**Formalization Note** Labels are per unit, as values are (the per-unit reduction of Assumption 2,
p.11): a buyer with demand `k_j` is `k_j` copies of its value with its label. The labels are random
and may be correlated with the values and with `N`; the proportions `ρ_i` are therefore not a
parameter but the law of the labels, and fixed proportions are a special case. Labels at indices
`≥ N ω` are ignored. CARA parameters are positive (`RiskModel.IsAdmissible`), since eq. (3) divides
by `α`. -/
structure HetMarket (Ω : Type*) [MeasurableSpace Ω] extends Market Ω where
  /-- Number of populations. -/
  k : ℕ
  k_pos : 0 < k
  /-- Population label of the `j`-th unit demanded in outcome `ω`. -/
  T : Ω → ℕ → Fin k
  measurable_T : ∀ j, Measurable fun ω => T ω j
  /-- The utility model shared by all populations. -/
  fam : RiskFamily
  /-- The risk-aversion parameter of each population (`α_i` or `β_i`). -/
  θ : Fin k → ℝ
  /-- `θ 0 ≤ θ 1 ≤ … ≤ θ (k − 1)` (p.19). -/
  θ_mono : Monotone θ
  /-- `β_i ≥ 0`, resp. `α_i > 0`. -/
  admissible : ∀ i, (fam.toModel (θ i)).IsAdmissible

namespace HetMarket

variable {Ω : Type*} [MeasurableSpace Ω] (H : HetMarket Ω)

/-- The risk model of population `i`. -/
def model (i : Fin H.k) : RiskModel :=
  H.fam.toModel (H.θ i)

/-- Population `k` of the paper, the most risk-averse one (index `k − 1`). -/
def last : Fin H.k :=
  ⟨H.k - 1, Nat.sub_lt H.k_pos Nat.one_pos⟩

/-- The labelled units of outcome `ω`: pairs (value, population). -/
def lunits (ω : Ω) : List (ℝ × Fin H.k) :=
  List.ofFn fun j : Fin (H.N ω) => (H.V ω j, H.T ω j)

/-- **Purchase rule of a labelled unit** at clearing-price law `h` and Market-Maker price `p`
(p.10: "Every buyer decides between the two purchase options by comparing his/her utility from each
option"; p.41: "we assume that such indifferent buyers will opt for the Market-Maker contract"): a
unit of value `v` and population `i` buys iff the published rule `buysMM (model i) h p v` holds
(`p ≤ v` and `U_A(v) ≤ U_buy(v, p)` under population `i`'s model). -/
def buys (h : Measure ℝ) (p : ℝ) (x : ℝ × Fin H.k) : Prop :=
  buysMM (H.model x.2) h p x.1

open Classical in
/-- Units bought through the Market-Maker contract at `(h, p)`. -/
noncomputable def mmUnits (h : Measure ℝ) (p : ℝ) (ω : Ω) : List (ℝ × Fin H.k) :=
  (H.lunits ω).filter fun x => decide (H.buys h p x)

open Classical in
/-- Units that stay in the auction at `(h, p)`. -/
noncomputable def restUnits (h : Measure ℝ) (p : ℝ) (ω : Ω) : List (ℝ × Fin H.k) :=
  (H.lunits ω).filter fun x => !decide (H.buys h p x)

/-- `ℓ`, the number of contract units at `(h, p)`. -/
noncomputable def nMM (h : Measure ℝ) (p : ℝ) (ω : Ω) : ℕ :=
  (H.mmUnits h p ω).length

/-- **Clearing price with the contract** at `(h, p)`: the `(I − ℓ + 1)`-th highest value among the
units that stay in the auction, `0` if there are at most `I − ℓ` of them (p.18: "I − ℓ buyers
participate in the auction in P2").

**Formalization Note** `I − ℓ` is truncated natural subtraction; it matters only when `ℓ > I`, where
the Market-Maker defaults and the price is not an equilibrium price (`IsEqPrice`). -/
noncomputable def c1 (h : Measure ℝ) (p : ℝ) (ω : Ω) : ℝ :=
  (sortDesc ((H.restUnits h p ω).map Prod.fst)).getD (H.I - H.nMM h p ω) 0

/-- **Efficiency with the contract** at `(h, p)`: the contract units plus the `I − ℓ` highest
remaining units (§3.4, p.13). -/
noncomputable def eff1 (h : Measure ℝ) (p : ℝ) (ω : Ω) : ℝ :=
  ((H.mmUnits h p ω).map Prod.fst).sum +
    ((sortDesc ((H.restUnits h p ω).map Prod.fst)).take (H.I - H.nMM h p ω)).sum

/-- **Revenue with the contract** at `(h, p)`: `ℓ · p + (I − ℓ) · c₁` (§3.4, p.13). -/
noncomputable def rev1 (h : Measure ℝ) (p : ℝ) (ω : Ω) : ℝ :=
  (H.nMM h p ω : ℝ) * p + ((H.I - H.nMM h p ω : ℕ) : ℝ) * H.c1 h p ω

open Classical in
/-- **Sum of the buyers' utilities with the contract** at `(h, p)`: a contract unit of value `v`
and population `i` gets `U_buy(v, p)` under model `i`, every other unit gets `U_A(v)` under model `i`
and the law `h`. -/
noncomputable def util1 (h : Measure ℝ) (p : ℝ) (ω : Ω) : ℝ :=
  ((H.lunits ω).map fun x =>
    if H.buys h p x then Ubuy (H.model x.2) x.1 p else UA (H.model x.2) h x.1).sum

/-- **Welfare with the contract** at `(h, p)` (§3.4, p.13). -/
noncomputable def welfare1 (h : Measure ℝ) (p : ℝ) (ω : Ω) : ℝ :=
  H.util1 h p ω + H.rev1 h p ω

/-- **Sum of the buyers' utilities without the contract**: each unit gets `U_A(v)` under its
population's model and the no-contract clearing-price law `g = H.priceLaw P`. -/
noncomputable def util0 (P : Measure Ω) (ω : Ω) : ℝ :=
  ((H.lunits ω).map fun x => UA (H.model x.2) (H.priceLaw P) x.1).sum

/-- **Welfare without the contract** (§3.4, p.13). -/
noncomputable def welfare0 (P : Measure Ω) (ω : Ω) : ℝ :=
  H.util0 P ω + H.rev0 ω

/-- **Equilibrium clearing-price law at Market-Maker price `p`** (p.10: "the set of buyers who
choose each purchase option, and how they bid in the auction, such that all buyers are mutually best
responding"): every unit chooses by the purchase rule under the law `h`, and `h` is the law of the
clearing price `c₁` those choices induce.

**Formalization Note** A fixed point: `h` is a probability measure on `ℝ` and `h = P ∘ c₁(h, p)⁻¹`.
The bids are truthful (Theorem 1), so the clearing price is `c₁`. -/
def IsEqLaw (P : Measure Ω) (h : Measure ℝ) (p : ℝ) : Prop :=
  IsProbabilityMeasure h ∧ h = P.map (H.c1 h p)

/-- **Equilibrium Market-Maker price** (p.10; Remark 1, p.16: if "more than I buyers would select
the Market-Maker contract … the Market-Maker would default, so that such Market-Maker prices will
not induce a two-period equilibrium"; p.17 and p.38: a price at which "at least one buyer selects
the Market-Maker contract"): some equilibrium law `h` at `p` has at most `I` contract units almost
surely and a positive probability that some unit buys the contract. -/
def IsEqPrice (P : Measure Ω) (p : ℝ) : Prop :=
  ∃ h : Measure ℝ, H.IsEqLaw P h p ∧ (∀ᵐ ω ∂P, H.nMM h p ω ≤ H.I) ∧
    0 < P {ω | 0 < H.nMM h p ω}

/-- **`p*_{M,k}`** (p.20: "the unique Market-Maker price that we would get from Proposition 1 if we
assume that all buyers originate from population k … calculated using Equation (3) with α = αk (or
β = βk)"): the published `pStar` of the most risk-averse model applied to the no-contract
clearing-price law `g`. -/
noncomputable def pStarK (P : Measure Ω) : ℝ :=
  pStar (H.model H.last) (H.priceLaw P)

end HetMarket

end Supplement

end MarketMakerAds


