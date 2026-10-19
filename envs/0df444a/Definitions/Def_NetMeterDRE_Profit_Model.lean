-- Prove2me | Definitions.Def_NetMeterDRE_Profit_Model
-- name    : NetMeterDRE_Profit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:36.193957+00:00
-- url     : https://prove2.me/theorems/be2f8b87-4ada-4e5e-9ffd-ce6a78ab7623
-- title:
--   §2, pp. 9–12, (4)(a), (5), (6), Definition 2; Appendix C, (EC.8), (EC.13), (EC.16), (EC.17) — utilities' profit under net metering, ν, ν̂, γr, γm
-- statement:
--   The utilities' side of the model of Sunar and Swaminathan. Utilities are indexed by a finite set $\mathcal I$, and all random quantities live on a probability space $(\Omega,\mathbb P)$.
--
--   **Data.** Utility $i$ sells to its end-customers at the retail price $p_{u,i}$. Its net-metered customers demand $D_i$ and generate $\Delta_i$ units of electricity (distributed renewable energy, DRE); its total end-customer demand is $\widehat D_i = \beta D_i$ with a constant $\beta$. It has existing resources that cover up to $K_i$ units at the unit cost $\tilde c$. The rest of the wholesale demand is a random variable $\xi$.
--
--   **Standing assumptions** (§2): $N > 2$, $c > 0$, $\beta > 1$, $\tilde c > 0$, $p_{u,i} > \tilde c$ for every $i$ ((4)(a)), and $K_i \ge 0$. The random variables $D_i$, $\Delta_i$, $\xi$ are measurable; $D_i$ and $\Delta_i$ take values in $[0, Q_i]$ and $\xi$ in $[\underline\eta, \bar\eta]$ almost surely; and $\mathbb E[\Delta_i] \le \mathbb E[\widehat D_i]$. A separate predicate states that region $j$'s pair $(D_j, \Delta_j)$ is independent of the other regions' pairs $(D_i,\Delta_i)_{i\ne j}$ together with $\xi$.
--
--   **Net wholesale demand (5):**
--   $$\mathcal D_w = \sum_{i} \big(\widehat D_i - K_i - \Delta_i\big) + \xi .$$
--
--   **Profit (6).** Under a net metering rule $\ell \in \{r, m\}$ the utility buys its customers' surplus $(\Delta_j - D_j)^+$ at $p_\ell$, where $p_r = p_{u,j}$ (retail-based rule) and $p_m = p^*_w$ (market-based rule). With the wholesale price $p^*_w = p_w(\mathcal D_w)$ for a price function $p_w$, utility $j$'s expected profit is
--   $$\begin{aligned}\Pi_j(\ell) ={}& \mathbb E\big[(\widehat D_j - D_j + (D_j-\Delta_j)^+)\,p_{u,j}\big] - \mathbb E\big[(\Delta_j - D_j)^+ p_\ell\big] \\ &- \mathbb E\big[\mathbb I\{\widehat D_j > \Delta_j + K_j\}\big((\widehat D_j - \Delta_j - K_j)p^*_w + K_j\tilde c\big)\big] \\ &+ \mathbb E\big[\mathbb I\{\widehat D_j \le K_j + \Delta_j\}\big((\Delta_j + K_j - \widehat D_j)p^*_w - K_j\tilde c\big)\big].\end{aligned}$$
--   **No DRE (Definition 2).** $\Pi_j(0)$ is the same expected profit when no end-customer in any region generates electricity, i.e. $\Delta_i \equiv 0$ for every $i$.
--
--   **The constants of Appendix C.**
--   $$\nu = \mathbb E\Big[\sum_{i\ne j}(\widehat D_i - \Delta_i - K_i) + \xi\Big],\qquad \widehat\nu = \mathbb E\Big[\sum_{i\ne j}(\widehat D_i - K_i) + \xi\Big],$$
--   $$\gamma_r = \frac{\mathbb E[\Delta_j]\,p_{u,j}}{\mathbb E\big[2\Delta_j\widehat D_j - \Delta_j^2 + \nu\Delta_j + \widehat D_j(\widehat\nu - \nu)\big]},$$
--   $$\gamma_m = \frac{\mathbb E\big[D_j - (D_j - \Delta_j)^+\big]\,p_{u,j}}{\mathbb E\big[2\Delta_j\widehat D_j - \Delta_j^2 + \nu\Delta_j + \widehat D_j(\widehat\nu - \nu) - (\Delta_j - D_j)^+(\widehat D_j - \Delta_j + \nu)\big]}.$$
--   Neither $\nu$, $\widehat\nu$ nor $\gamma_\ell$ depends on $K_j$.
--
--   These objects are the vocabulary of Theorem 1, Corollaries 1–2 and Lemmas EC.1 and EC.3.
--
--   **Formalization Note** The four expectations of (6) are written as one expectation of their sum; under the standing assumptions every term is integrable. $(x)^+$ is $\max(x,0)$ and the indicators are `if … then … else 0` with the page's strict/non-strict inequalities. The rule $\ell = 0$ is not a third rule but the profit evaluated with $\Delta \equiv 0$ in every region. $\gamma_\ell$ is stored as numerator over denominator; Lean's real division returns $0$ when the denominator is $0$. The independence of region $j$ from the rest of the market is not stated in the paper but is used by its proofs; it is a separate predicate so that each theorem lists it explicitly. Condition (4)(b), condition (7) and the differentiability of the distribution functions are not part of the standing assumptions (see the theorems' notes). The market with utility $j$'s resources set to $k$ (all other data unchanged) is `U.setK j k`.
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), pp. 7–12 (PDF 7–12), §2, (4)(a), (5), (6), Definition 2; pp. ec4–ec5 (PDF 36–37), (EC.8), (EC.13), (EC.16), (EC.17)

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE

namespace NetMeterDRE.Profit

open MeasureTheory ProbabilityTheory

/-! # Utilities under net metering (Sunar & Swaminathan, SSRN 3257925, §2, pp. 9–12;
Appendix C, pp. ec4–ec5)

Utilities are indexed by a finite type `ι`. Utility `i`'s end-customer demand is
`D̂ i = β · D i`, where `D i` is the demand of its net-metered customers, who generate `Δ i`.
The utility holds existing resources `K i` at unit cost `c̃` and sells at the retail price
`pu i`. `ξ` is the rest of the wholesale demand. -/

/-- The two net metering rules: `r` (buy-back at the retail price) and `m` (buy-back at the
wholesale price). The no-DRE case `ℓ = 0` of Definition 2 is not a rule of this type: it is
the profit (6) evaluated with zero generation in every region (`noDREProfit`). -/
inductive Rule
  | r
  | m

/-- The deterministic data of the utilities' side of the market. -/
structure Market (ι : Type*) where
  /-- `β`, with `D̂ i = β · D i`. -/
  beta : ℝ
  /-- Retail prices `p_{u,i}`. -/
  pu : ι → ℝ
  /-- The unit cost `c̃` of existing resources. -/
  ct : ℝ
  /-- Existing resources `K i`. -/
  K : ι → ℝ
  /-- `[0, Q i]` is the support of `D i` and of `Δ i`. -/
  Q : ι → ℝ
  /-- `[η̲, η̄]` is the support of `ξ`. -/
  etaLo : ℝ
  etaHi : ℝ

/-- The market with utility `j`'s existing resources set to `k`, every other datum unchanged. -/
def Market.setK {ι : Type*} [DecidableEq ι] (U : Market ι) (j : ι) (k : ℝ) : Market ι :=
  { U with K := Function.update U.K j k }

/-- The standing deterministic assumptions of §2: `N > 2` generators (p. 7), generation cost
coefficient `c > 0` (p. 8), `β > 1` (p. 9), `c̃ > 0` and `Kᵢ ≥ 0` (p. 9), and
`p_{u,i} > c̃` for every `i` ((4)(a), p. 10). -/
def Standing {ι : Type*} (N : ℕ) (c : ℝ) (U : Market ι) : Prop :=
  2 < N ∧ 0 < c ∧ 1 < U.beta ∧ 0 < U.ct ∧ (∀ i, U.ct < U.pu i) ∧ (∀ i, 0 ≤ U.K i)

/-- The standing assumptions on the random primitives (§2, pp. 9–11): `D i`, `Δ i`, `ξ` are
measurable; `D i` and `Δ i` take values in `[0, Q i]` almost surely, `ξ` in `[η̲, η̄]`
almost surely; and `E[Δ i] ≤ E[D̂ i]`. -/
def Primitives {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Market ι)
    (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) : Prop :=
  (∀ i, Measurable (D i)) ∧ (∀ i, Measurable (Δ i)) ∧ Measurable ξ ∧
  (∀ i, ∀ᵐ ω ∂P, D i ω ∈ Set.Icc 0 (U.Q i)) ∧
  (∀ i, ∀ᵐ ω ∂P, Δ i ω ∈ Set.Icc 0 (U.Q i)) ∧
  (∀ᵐ ω ∂P, ξ ω ∈ Set.Icc U.etaLo U.etaHi) ∧
  (∀ i, ∫ ω, Δ i ω ∂P ≤ ∫ ω, U.beta * D i ω ∂P)

/-- Region `j`'s pair `(D j, Δ j)` is independent of the other regions' pairs together
with `ξ`. (Added: the proof in Appendix C uses it to replace the rest of the market by its
mean `ν`, `ν̂`.) -/
def RegionIndep {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D Δ : ι → Ω → ℝ)
    (ξ : Ω → ℝ) (j : ι) : Prop :=
  IndepFun (fun ω => (D j ω, Δ j ω))
    (fun ω => ((fun i : {i // i ≠ j} => (D i.1 ω, Δ i.1 ω)), ξ ω)) P

/-- (5): the net wholesale demand `D_w = ∑ᵢ (D̂ᵢ − Kᵢ − Δᵢ) + ξ`. -/
def netDemand {ι Ω : Type*} [Fintype ι] (U : Market ι) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ)
    (ω : Ω) : ℝ :=
  ∑ i, (U.beta * D i ω - U.K i - Δ i ω) + ξ ω

/-- `p_ℓ` (p. 11): the buy-back price, `p_{u,j}` under `r` and the wholesale price `p` under `m`. -/
def buybackPrice {ι : Type*} (U : Market ι) (ℓ : Rule) (j : ι) (p : ℝ) : ℝ :=
  match ℓ with
  | .r => U.pu j
  | .m => p

/-- The integrand of (6) for utility `j`, when the wholesale price is `pw (D_w)`:
`(D̂ⱼ − Dⱼ + (Dⱼ − Δⱼ)⁺) p_{u,j} − (Δⱼ − Dⱼ)⁺ p_ℓ
 − 𝟙{D̂ⱼ > Δⱼ + Kⱼ} ((D̂ⱼ − Δⱼ − Kⱼ) p*_w + Kⱼ c̃)
 + 𝟙{D̂ⱼ ≤ Kⱼ + Δⱼ} ((Δⱼ + Kⱼ − D̂ⱼ) p*_w − Kⱼ c̃)`. -/
noncomputable def profitIntegrand {ι Ω : Type*} [Fintype ι] (U : Market ι) (pw : ℝ → ℝ) (ℓ : Rule) (j : ι)
    (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) (ω : Ω) : ℝ :=
  (U.beta * D j ω - D j ω + max (D j ω - Δ j ω) 0) * U.pu j
  - max (Δ j ω - D j ω) 0 * buybackPrice U ℓ j (pw (netDemand U D Δ ξ ω))
  - (if Δ j ω + U.K j < U.beta * D j ω then
      (U.beta * D j ω - Δ j ω - U.K j) * pw (netDemand U D Δ ξ ω) + U.K j * U.ct else 0)
  + (if U.beta * D j ω ≤ U.K j + Δ j ω then
      (Δ j ω + U.K j - U.beta * D j ω) * pw (netDemand U D Δ ξ ω) - U.K j * U.ct else 0)

/-- `Π_j(ℓ)`, (6): utility `j`'s expected profit under the net metering rule `ℓ`. -/
noncomputable def expProfit {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω)
    (U : Market ι) (pw : ℝ → ℝ) (ℓ : Rule) (j : ι) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) : ℝ :=
  ∫ ω, profitIntegrand U pw ℓ j D Δ ξ ω ∂P

/-- `Π_j(0)`, Definition 2: utility `j`'s expected profit when no end-customer in any region
generates electricity (`Δ ≡ 0`); the buy-back rule is then immaterial. -/
noncomputable def noDREProfit {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω)
    (U : Market ι) (pw : ℝ → ℝ) (j : ι) (D : ι → Ω → ℝ) (ξ : Ω → ℝ) : ℝ :=
  expProfit P U pw .r j D (fun _ _ => 0) ξ

/-- `ν`, (EC.8): `E[∑_{i≠j} (D̂ᵢ − Δᵢ − Kᵢ) + ξ]`. -/
noncomputable def nu {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) (U : Market ι) (j : ι) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) : ℝ :=
  ∫ ω, (∑ i ∈ Finset.univ.erase j, (U.beta * D i ω - Δ i ω - U.K i) + ξ ω) ∂P

/-- `ν̂`, (EC.13): `E[∑_{i≠j} (D̂ᵢ − Kᵢ) + ξ]`. -/
noncomputable def nuHat {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) (U : Market ι) (j : ι) (D : ι → Ω → ℝ) (ξ : Ω → ℝ) : ℝ :=
  ∫ ω, (∑ i ∈ Finset.univ.erase j, (U.beta * D i ω - U.K i) + ξ ω) ∂P

/-- Numerators of (EC.16)/(EC.17): `E[Δⱼ] p_{u,j}` for `r`,
`E[Dⱼ − (Dⱼ − Δⱼ)⁺] p_{u,j}` for `m`. -/
noncomputable def gammaNum {ι Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Market ι)
    (ℓ : Rule) (j : ι) (D Δ : ι → Ω → ℝ) : ℝ :=
  match ℓ with
  | .r => (∫ ω, Δ j ω ∂P) * U.pu j
  | .m => (∫ ω, (D j ω - max (D j ω - Δ j ω) 0) ∂P) * U.pu j

/-- Denominators of (EC.16)/(EC.17):
`E[2ΔⱼD̂ⱼ − Δⱼ² + νΔⱼ + D̂ⱼ(ν̂ − ν)]` for `r`, and the same minus
`(Δⱼ − Dⱼ)⁺(D̂ⱼ − Δⱼ + ν)` inside the expectation for `m`. -/
noncomputable def gammaDen {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) (U : Market ι) (ℓ : Rule) (j : ι) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) : ℝ :=
  match ℓ with
  | .r => ∫ ω, (2 * Δ j ω * (U.beta * D j ω) - Δ j ω ^ 2 + nu P U j D Δ ξ * Δ j ω
              + U.beta * D j ω * (nuHat P U j D ξ - nu P U j D Δ ξ)) ∂P
  | .m => ∫ ω, (2 * Δ j ω * (U.beta * D j ω) - Δ j ω ^ 2 + nu P U j D Δ ξ * Δ j ω
              + U.beta * D j ω * (nuHat P U j D ξ - nu P U j D Δ ξ)
              - max (Δ j ω - D j ω) 0 * (U.beta * D j ω - Δ j ω + nu P U j D Δ ξ)) ∂P

/-- `γ_ℓ`, (EC.16) for `ℓ = r` and (EC.17) for `ℓ = m`. -/
noncomputable def gamma {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (P : Measure Ω) (U : Market ι) (ℓ : Rule) (j : ι) (D Δ : ι → Ω → ℝ) (ξ : Ω → ℝ) : ℝ :=
  gammaNum P U ℓ j D Δ / gammaDen P U ℓ j D Δ ξ

end NetMeterDRE.Profit


