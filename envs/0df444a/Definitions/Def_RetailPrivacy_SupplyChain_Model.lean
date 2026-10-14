-- Prove2me | Definitions.Def_RetailPrivacy_SupplyChain_Model
-- name    : RetailPrivacy_SupplyChain_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:06.592168+00:00
-- url     : https://prove2.me/theorems/34333a5e-e53f-4743-81af-bd6376e4ef2f
-- title:
--   §3, §4.1–4.2, §5, pp. 8–19 — uniform inconvenience cost, utility (1), ℝ/ℂ data policies, rational-expectations disclosure, three-stage supplier–retailer game
-- statement:
--   The model of Xu, Wang and Zhang's online retail supply chain with consumer data.
--
--   **Consumers.** A unit mass of consumers values the product at $v$. A consumer's inconvenience cost $\theta$ is uniform on $[0,1]$. The data quality is $\delta \in (0,1)$ and the retailer's monetization cost parameter is $c > 0$. A consumer who buys at price $p$ and hides her data gets $v - p - \theta$; one who buys and discloses gets $v - p - (1-\delta)\theta - r\delta$, where $r \ge 0$ is the retailer's data-monetization intensity (utility (1), p. 10). If the retailer collects data ($\ell = 1$), a buyer takes the better of hiding and disclosing; without collection ($\ell = 0$) only hiding is available. A consumer buys iff her best buying utility is non-negative and, among buyers, discloses iff disclosing is weakly better.
--
--   The **demand** (sales quantity) is the Lebesgue measure of buyers in $[0,1]$, the **disclosing quantity** $s$ the measure of buyers who disclose, and the **consumer surplus** is
--   $$\mathrm{CS} = \int_0^1 \max\{0,\ U(\theta)\}\,d\theta,$$
--   where $U(\theta)$ is the consumer's best buying utility. The retailer's **downside exploitation profit** is $r\delta s - c r^2$ (p. 11). The constants of the paper are
--   $$\mathcal Z = 2c+\delta,\quad \mathcal M = 4c^2(1-\delta) + c\delta(4-3\delta) + \delta^2,\quad \mathcal F = 4c^2(1-\delta) + 4c\delta(1-\delta) + \delta^2 .$$
--
--   **Data policies.** In the **ℝ mode** (retailer-controlled, before the GDPR) the retailer chooses $r$ after the data are collected, as a best response $r \in \arg\max_{r' \ge 0} (r'\delta s - c r'^2)$ to the disclosing quantity $s$, and consumers' expectation of $s$ is correct: $s$ is the disclosing quantity given $r$ (rational expectations equilibrium, p. 13). In the **ℂ mode** (consumer-controlled, the GDPR) exploitation is blocked: $r = 0$ and $s$ is the disclosing quantity at $r = 0$. Without collection $s = r = 0$.
--
--   **Supply chain game** (§5, Figure 2). The retailer chooses $\ell$; the supplier (production cost zero) sets the wholesale price $w$; the retailer sets the retail price $p$; then the consumer stage is played. The retailer's profit is $(p-w)\cdot\text{demand} + r\delta s - c r^2$ (4) and the supplier's is $w\cdot\text{demand}$ (p. 19). A **strategy profile** specifies $\ell$, a wholesale price after each $\ell$, a retail price after each $(\ell, w)$, and a consumer-stage outcome $(s,r)$ after each $(\ell, p)$. It is a **subgame-perfect equilibrium** under a policy if (1) the consumer stage is an REE at every $(\ell, p)$; (2) at every $(\ell, w)$ the retail price maximizes the retailer's profit over all $p \in \mathbb R$; (3) after each $\ell$ the wholesale price maximizes the supplier's profit over all $w \in \mathbb R$, against the retailer's pricing strategy; (4) $\ell$ maximizes the retailer's subgame profit. The equilibrium outcomes (retailer profit, supplier profit, consumer surplus) are evaluated on the path at the chosen $\ell$.
--
--   This file is the common substrate of every statement of the mission.
--
--   **Formalization Note** The policy is `Policy.R`/`Policy.C`, collection is a `Bool`. Demand and disclosing quantity are `(volume S).toReal` of θ-sets in $[0,1]$; ties go to buying and to disclosing (null sets). Consumer surplus is the interval integral of `max 0 (buyUtil …)`. Strategies are total functions, so off-path behaviour is specified at every node; prices range over all of $\mathbb R$ and the maximizations are `∀`-comparisons. The consumer-stage part is textually identical, up to the namespace, to the single-firm mission's model.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), pp. 8–13, 15, 17, 19, utility (1), profit (4), Figure 2

import Mathlib
import Definitions.Def_RetailPrivacy_SingleFirm_Model

namespace RetailPrivacy.SupplyChain

/-! ### Consumer stage (§3, §4.1–4.2): imported from the shared module `RetailPrivacy.SingleFirm.Model`
(`Policy`, `Zc`, `Mc`, `Fc`, `buyUtil`, `demand`, `discloseQty`, `consumerSurplus`, `dataProfit`, `IsREE`). -/

/-! ### Supply chain game (§5) -/

/-- A strategy profile of the three-stage game, with actions at every node (off-path included):
the retailer's collection decision, the supplier's wholesale price after each `ℓ`, the retailer's
retail price after each `(ℓ, w)`, and the consumer-stage outcome `(s, r)` after each `(ℓ, p)`. -/
structure Profile where
  collect : Bool
  wholesale : Bool → ℝ
  price : Bool → ℝ → ℝ
  resp : Bool → ℝ → ℝ × ℝ

/-- Retailer profit (4): `(p − w)·RetailPrivacy.SingleFirm.demand + rδs − cr²`, with `(s, r) = sr`. -/
noncomputable def retailerProfit (ℓ : Bool) (v c δ w p : ℝ) (sr : ℝ × ℝ) : ℝ :=
  (p - w) * RetailPrivacy.SingleFirm.demand ℓ v δ p sr.2 + RetailPrivacy.SingleFirm.dataProfit c δ sr.1 sr.2

/-- Supplier profit `w·RetailPrivacy.SingleFirm.demand` (production cost zero). -/
noncomputable def supplierProfit (ℓ : Bool) (v δ w p : ℝ) (sr : ℝ × ℝ) : ℝ :=
  w * RetailPrivacy.SingleFirm.demand ℓ v δ p sr.2

/-- The wholesale price on the path after `ℓ`. -/
def pathWholesale (P : Profile) (ℓ : Bool) : ℝ := P.wholesale ℓ

/-- The retail price on the path after `ℓ`. -/
def pathPrice (P : Profile) (ℓ : Bool) : ℝ := P.price ℓ (P.wholesale ℓ)

/-- The consumer-stage outcome `(s, r)` on the path after `ℓ`. -/
def pathResp (P : Profile) (ℓ : Bool) : ℝ × ℝ := P.resp ℓ (pathPrice P ℓ)

/-- The retailer's profit in the subgame after `ℓ`, along the profile. -/
noncomputable def retailerValue (v c δ : ℝ) (P : Profile) (ℓ : Bool) : ℝ :=
  retailerProfit ℓ v c δ (pathWholesale P ℓ) (pathPrice P ℓ) (pathResp P ℓ)

/-- The supplier's profit in the subgame after `ℓ`, along the profile. -/
noncomputable def supplierValue (v δ : ℝ) (P : Profile) (ℓ : Bool) : ℝ :=
  supplierProfit ℓ v δ (pathWholesale P ℓ) (pathPrice P ℓ) (pathResp P ℓ)

/-- The consumer surplus in the subgame after `ℓ`, along the profile. -/
noncomputable def surplusValue (v δ : ℝ) (P : Profile) (ℓ : Bool) : ℝ :=
  RetailPrivacy.SingleFirm.consumerSurplus ℓ v δ (pathPrice P ℓ) (pathResp P ℓ).2

/-- Subgame-perfect equilibrium of the supply chain game under policy `pol`: the consumer stage
is an REE at every `(ℓ, p)`; the retail price is a best response over all `p ∈ ℝ` at every
`(ℓ, w)`; the wholesale price is a best response over all `w ∈ ℝ` against the retailer's
strategy, after each `ℓ`; and `collect` maximizes the retailer's subgame profit over `ℓ`. -/
def IsSPE (pol : RetailPrivacy.SingleFirm.Policy) (v c δ : ℝ) (P : Profile) : Prop :=
  (∀ ℓ p, RetailPrivacy.SingleFirm.IsREE pol ℓ v c δ p (P.resp ℓ p).1 (P.resp ℓ p).2) ∧
  (∀ ℓ w p', retailerProfit ℓ v c δ w p' (P.resp ℓ p')
      ≤ retailerProfit ℓ v c δ w (P.price ℓ w) (P.resp ℓ (P.price ℓ w))) ∧
  (∀ ℓ w', supplierProfit ℓ v δ w' (P.price ℓ w') (P.resp ℓ (P.price ℓ w'))
      ≤ supplierValue v δ P ℓ) ∧
  (∀ ℓ', retailerValue v c δ P ℓ' ≤ retailerValue v c δ P P.collect)

/-- Equilibrium retailer profit (on the path, at `ℓ = collect`). -/
noncomputable def eqRetailer (v c δ : ℝ) (P : Profile) : ℝ := retailerValue v c δ P P.collect

/-- Equilibrium supplier profit (on the path). -/
noncomputable def eqSupplier (v δ : ℝ) (P : Profile) : ℝ := supplierValue v δ P P.collect

/-- Equilibrium consumer surplus (on the path). -/
noncomputable def eqCS (v δ : ℝ) (P : Profile) : ℝ := surplusValue v δ P P.collect

end RetailPrivacy.SupplyChain


