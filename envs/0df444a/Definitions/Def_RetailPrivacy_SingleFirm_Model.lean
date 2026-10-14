-- Prove2me | Definitions.Def_RetailPrivacy_SingleFirm_Model
-- name    : RetailPrivacy_SingleFirm_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:55.928031+00:00
-- url     : https://prove2.me/theorems/45cc614a-875b-4a84-baf6-e71bb2da7c88
-- title:
--   §3, §4, pp. 8–17 — uniform inconvenience cost, utility (1), ℝ/ℂ data policies, rational-expectations disclosure, single-firm collection-then-pricing game
-- statement:
--   This file sets up the single-firm model of Xu, Wang and Zhang.
--
--   **Parameters.** A unit mass of consumers values the product at $v$. A consumer's inconvenience cost $\theta$ is uniform on $[0,1]$. The data quality is $\delta \in (0,1)$ and the monetization cost coefficient is $c > 0$. The constants of the paper are
--   $$\mathcal Z = 2c+\delta,\qquad \mathcal M = 4c^2(1-\delta)+c\delta(4-3\delta)+\delta^2,\qquad \mathcal F = 4c^2(1-\delta)+4c\delta(1-\delta)+\delta^2 .$$
--
--   **Data policies.** The $\mathbb R$ mode (retailer-controlled, before the GDPR) and the $\mathbb C$ mode (consumer-controlled, the GDPR). The firm's collection decision is $\ell \in \{0,1\}$.
--
--   **Consumers.** At price $p$ and monetization intensity $r$, a buyer who hides her data gets $v-p-\theta$ and a buyer who discloses gets $v-p-(1-\delta)\theta-r\delta$. Without collection only hiding is available. A consumer buys iff her best buying utility is nonnegative, and among buyers she discloses iff disclosing is weakly better than hiding. The **demand** is the Lebesgue measure of the buyers' $\theta$ in $[0,1]$, the **disclosing quantity** the measure of the disclosing buyers, and the **consumer surplus** is
--   $$CS = \int_0^1 \max\{0,\ \text{best buying utility of } \theta\}\,d\theta .$$
--
--   **Exploitation and rational expectations.** The firm's exploitation profit is $r\delta s - c r^2$. After collection under the $\mathbb R$ mode, a pair $(s,r)$ is a rational expectations equilibrium if $r$ maximizes $r'\delta s - c r'^2$ over $r' \ge 0$ and $s$ equals the disclosing quantity induced by $r$. Under the $\mathbb C$ mode $r = 0$ and $s$ is the disclosing quantity at $r = 0$. Without collection $s = r = 0$.
--
--   **The game.** A strategy profile specifies the collection decision $\ell^*$, a price for each $\ell$, and an equilibrium response $(s,r)$ after every $(\ell,p)$, $p \in \mathbb R$. The firm's profit is $p\cdot\text{demand} + r\delta s - c r^2$. A **subgame-perfect equilibrium** has an REE response at every $(\ell,p)$, a profit-maximizing price over all of $\mathbb R$ for each $\ell$, and a profit-maximizing $\ell^*$. Its on-path price, response, profit, consumer surplus and social welfare (profit plus consumer surplus) are the objects compared in Theorem 1.
--
--   **Formalization Note** Sets of consumers are measured by `(volume S).toReal` on $[0,1]$; indifferent consumers buy and disclose (null sets). The profit is defined from the REE, not from the paper's (3), which uses the unsaturated $r(p)$ of (2). The consumer-stage part is textually the same as in the companion supply-chain mission, up to the namespace.
-- source:
--   Xu, Wang & Zhang, Consumer Privacy in Online Retail Supply Chains, author manuscript (Management Science, forthcoming; version of November 2024), pp. 8–13, 15, 17, (1), (3), Figure 2

import Mathlib

namespace RetailPrivacy.SingleFirm

noncomputable section

/-- The data policy: `R` is the retailer-controlled mode (pre-GDPR), `C` the
consumer-controlled mode (the GDPR). -/
inductive Policy
  | R
  | C
  deriving DecidableEq

/-- 𝒵 = 2c + δ (p. 13). -/
def Zc (c δ : ℝ) : ℝ := 2 * c + δ

/-- ℳ = 4c²(1 − δ) + cδ(4 − 3δ) + δ² (p. 13). -/
def Mc (c δ : ℝ) : ℝ := 4 * c ^ 2 * (1 - δ) + c * δ * (4 - 3 * δ) + δ ^ 2

/-- ℱ = 4c²(1 − δ) + 4cδ(1 − δ) + δ² (p. 17). -/
def Fc (c δ : ℝ) : ℝ := 4 * c ^ 2 * (1 - δ) + 4 * c * δ * (1 - δ) + δ ^ 2

/-- Utility of buying and hiding data: v − p − θ. -/
def utilHide (v p θ : ℝ) : ℝ := v - p - θ

/-- Utility of buying and disclosing data: v − p − (1 − δ)θ − rδ. -/
def utilDisclose (v δ p r θ : ℝ) : ℝ := v - p - (1 - δ) * θ - r * δ

/-- A buyer's best utility: with collection (`ℓ = true`) she may hide or disclose;
without collection only hiding is available. -/
def buyUtil (ℓ : Bool) (v δ p r θ : ℝ) : ℝ :=
  if ℓ then max (utilHide v p θ) (utilDisclose v δ p r θ) else utilHide v p θ

/-- Demand: the mass of θ ∈ [0, 1] whose best buying utility is nonnegative. -/
def demand (ℓ : Bool) (v δ p r : ℝ) : ℝ :=
  (MeasureTheory.volume {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ 0 ≤ buyUtil ℓ v δ p r θ}).toReal

/-- Disclosing quantity: the mass of θ ∈ [0, 1] who weakly prefer disclosing to hiding
and get a nonnegative utility from buying and disclosing. -/
def discloseQty (v δ p r : ℝ) : ℝ :=
  (MeasureTheory.volume {θ : ℝ | θ ∈ Set.Icc 0 1 ∧ utilHide v p θ ≤ utilDisclose v δ p r θ ∧
    0 ≤ utilDisclose v δ p r θ}).toReal

/-- Consumer surplus: each consumer's realized utility (0 if she does not buy),
integrated over θ uniform on [0, 1]. -/
def consumerSurplus (ℓ : Bool) (v δ p r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..1, max 0 (buyUtil ℓ v δ p r θ)

/-- The downside exploitation profit rδs − cr² (p. 11). -/
def dataProfit (c δ s r : ℝ) : ℝ := r * δ * s - c * r ^ 2

/-- Rational expectations equilibrium (s, r) of the consumer stage and the exploitation
stage after the collection decision ℓ and the price p. -/
def IsREE (pol : Policy) (ℓ : Bool) (v c δ p s r : ℝ) : Prop :=
  if ℓ then
    match pol with
    | .R => IsMaxOn (fun r' => dataProfit c δ s r') (Set.Ici 0) r ∧ s = discloseQty v δ p r
    | .C => r = 0 ∧ s = discloseQty v δ p 0
  else s = 0 ∧ r = 0

/-- A strategy profile of the single-firm game: the collection decision, the price after
each collection decision, and the consumer/exploitation response (s, r) after every
(ℓ, p). -/
structure Profile where
  collect : Bool
  price : Bool → ℝ
  resp : Bool → ℝ → ℝ × ℝ

/-- The firm's profit p · demand + rδs − cr² at (ℓ, p) given the response (s, r). -/
def firmProfit (ℓ : Bool) (v c δ p : ℝ) (sr : ℝ × ℝ) : ℝ :=
  p * demand ℓ v δ p sr.2 + dataProfit c δ sr.1 sr.2

/-- Subgame-perfect equilibrium of the single-firm game under the policy `pol`. -/
def IsSPE (pol : Policy) (v c δ : ℝ) (P : Profile) : Prop :=
  (∀ ℓ p, IsREE pol ℓ v c δ p (P.resp ℓ p).1 (P.resp ℓ p).2) ∧
  (∀ ℓ p', firmProfit ℓ v c δ p' (P.resp ℓ p') ≤
    firmProfit ℓ v c δ (P.price ℓ) (P.resp ℓ (P.price ℓ))) ∧
  (∀ ℓ', firmProfit ℓ' v c δ (P.price ℓ') (P.resp ℓ' (P.price ℓ')) ≤
    firmProfit P.collect v c δ (P.price P.collect) (P.resp P.collect (P.price P.collect)))

/-- On-path price. -/
def eqPrice (P : Profile) : ℝ := P.price P.collect

/-- On-path response (s, r). -/
def eqResp (P : Profile) : ℝ × ℝ := P.resp P.collect (eqPrice P)

/-- On-path profit of the firm. -/
def eqProfit (v c δ : ℝ) (P : Profile) : ℝ := firmProfit P.collect v c δ (eqPrice P) (eqResp P)

/-- On-path consumer surplus. -/
def eqCS (v δ : ℝ) (P : Profile) : ℝ := consumerSurplus P.collect v δ (eqPrice P) (eqResp P).2

/-- On-path social welfare: the firm's profit plus the consumer surplus. -/
def eqWelfare (v c δ : ℝ) (P : Profile) : ℝ := eqProfit v c δ P + eqCS v δ P

end

end RetailPrivacy.SingleFirm


