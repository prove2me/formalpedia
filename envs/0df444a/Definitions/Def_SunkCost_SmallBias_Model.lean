-- Prove2me | Definitions.Def_SunkCost_SmallBias_Model
-- name    : SunkCost_SmallBias_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:06.260715+00:00
-- url     : https://prove2.me/theorems/af3d9d7e-de08-4574-a075-4286dfdfe5a7
-- title:
--   §4–§4.2, pp. 7–10 — present-biased consumers with sunk-cost bias: usage and purchase rules, demand, profit, long-run welfare, optimal price
-- statement:
--   This is the monopoly model of Jain and Chen (§4–§4.2). A monopolist sells a durable product at a price $p$. Consumer valuations $v$ are distributed according to a distribution function $F$ with support $(0,1)$. To obtain the value, the consumer must exert an effort later: with probability $\alpha$ the effort cost is low, $\kappa\in(0,1)$, and with probability $1-\alpha$ it is $1$. Consumers discount quasi-hyperbolically with present-bias parameter $\beta$ (and exponential discount $\delta=1$), and a consumer who paid $p$ and does not use the product suffers a sunk-cost discomfort $-\lambda p$, where $\lambda\ge 0$ is the sunk-cost bias. The firm has marginal cost $c$.
--
--   **Standing assumptions.** $0<\alpha\le 1$, $0<\kappa<1$, $\kappa<\beta\le 1$ and $c\ge 0$.
--
--   **Usage.** A consumer with valuation $v$ who paid $p$ uses the product under the low cost iff $\beta v-\kappa+\lambda p\ge 0$, i.e. $v\ge v_1$, and under the high cost iff $\beta v-1+\lambda p>0$, i.e. $v>v_2$, where
--
--   $$v_1=\frac{\kappa-\lambda p}{\beta},\qquad v_2=\frac{1-\lambda p}{\beta}.$$
--
--   **Purchase.** The consumer anticipates this usage and evaluates the purchase with long-run preferences:
--
--   $$U(v)=\alpha\,(v-\kappa)\,\mathbf 1[\text{uses at low cost}]+(1-\alpha)\,(v-1)\,\mathbf 1[\text{uses at high cost}]-p,$$
--
--   which equals $U_l=\alpha(v-\kappa)-p$ of (2) for a consumer who uses the product only under the low cost, and $U_h=v-\alpha\kappa-(1-\alpha)-p$ of (3) for one who always uses it. The consumers with $v\in[0,1]$ and $U(v)>0$ buy. The demand $D(p)$ is the $F$-probability of the set of buyers, and the profit is $(p-c)D(p)$.
--
--   **Welfare and optimal price.** Consumer welfare is the integral of $U$ over the buyers with respect to $F$ (long-run preferences, $\beta=1$, at the actual usage), and social welfare is consumer welfare plus profit. An optimal price is a $p\ge 0$ that maximizes profit over all prices $p'\ge 0$.
--
--   **Thresholds.** $v_3=p/\alpha+\kappa$, $v_4=p+\alpha\kappa+(1-\alpha)$, $\hat p_a=\kappa(1-\beta)\alpha/(\lambda\alpha+\beta)$, $\lambda_1=(1-\beta)/(\alpha(1-\kappa))$ (the bound in Proposition 1), and the objective $(p-c)(1-F(v_3))$ of (7).
--
--   These definitions are the common language of the demand formulas (4) and (5), the optimal price, and the welfare comparative statics of Proposition 3.
--
--   **Formalization Note.** "$F$ with support $(0,1)$" is encoded as: $F$ is a continuous Stieltjes function, $F=0$ on $(-\infty,0]$, $F=1$ on $[1,\infty)$, and $F$ is strictly increasing on $[0,1]$. Demand is the measure of the primitive buyer set, not formula (4) or (5). The utility $U$ omits the discomfort $-\lambda p$, exactly as (2) and (3) do. The paper never displays social welfare; it is read as consumer welfare plus profit. The tie-breaks ($\ge$ for low-cost usage, $>$ for high-cost usage and for purchase) are those printed on p. 8. The bias $\lambda$ is not part of the parameter record; each theorem states its range. All quantities are real numbers.
-- source:
--   Jain and Chen, Sunk cost bias and time inconsistency: a strategic analysis of pricing decisions, Management Science, Articles in Advance (2022), doi:10.1287/mnsc.2022.4479, pp. 7–10 (PDF 8–11), §4, §4.1, §4.2, (1)–(4), (7), Proposition 1 (p̂a, λ1)

import Mathlib

namespace SunkCost.SmallBias

open MeasureTheory

/-- The primitive parameters of the model of Jain and Chen, §4 (pp. 7–8):
`α` is the probability that the effort cost is low, `κ` the low effort cost (the high
cost is `1`), `β` the quasi-hyperbolic present-bias parameter (the exponential discount
`δ` is fixed to `1`, p. 7), and `c` the firm's marginal cost (p. 10). -/
structure Params where
  α : ℝ
  κ : ℝ
  β : ℝ
  c : ℝ

/-- The standing assumptions of §4 and §4.1 (pp. 7–8): `0 < α ≤ 1`, `0 < κ < 1`,
`κ < β ≤ 1`, and a nonnegative marginal cost `c ≥ 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.α ∧ P.α ≤ 1 ∧ 0 < P.κ ∧ P.κ < 1 ∧ P.κ < P.β ∧ P.β ≤ 1 ∧ 0 ≤ P.c

/-- "`v` varies across consumers according to a distribution `F(·)` with support `(0, 1)`"
(p. 7): `F` is a continuous distribution function, equal to `0` on `(-∞, 0]`, to `1` on
`[1, ∞)`, and strictly increasing on `[0, 1]`. -/
def ValuationCDF (F : StieltjesFunction ℝ) : Prop :=
  Continuous F ∧ (∀ x : ℝ, x ≤ 0 → F x = 0) ∧ (∀ x : ℝ, 1 ≤ x → F x = 1) ∧
    StrictMonoOn F (Set.Icc 0 1)

/-- Period-2 usage under the low cost `κ` (p. 8): a consumer with valuation `v` who paid
`p` uses the product iff `βv − κ + λp ≥ 0`. -/
def UsesLow (P : Params) (lam p v : ℝ) : Prop := 0 ≤ P.β * v - P.κ + lam * p

/-- Period-2 usage under the high cost `1` (p. 8): the consumer uses the product iff
`βv − 1 + λp > 0`. -/
def UsesHigh (P : Params) (lam p v : ℝ) : Prop := 0 < P.β * v - 1 + lam * p

open Classical in
/-- The anticipated utility of buying at price `p`, evaluated with long-run preferences
(`β = 1`, `δ = 1`) at the consumer's actual period-2 usage, as in (2) and (3) (p. 8):
`α(v − κ)·[uses under low cost] + (1 − α)(v − 1)·[uses under high cost] − p`.
The sunk-cost discomfort `−λp` is not part of it, as in (2) and (3). -/
noncomputable def utility (P : Params) (lam p v : ℝ) : ℝ :=
  P.α * (if UsesLow P lam p v then v - P.κ else 0)
    + (1 - P.α) * (if UsesHigh P lam p v then v - 1 else 0) - p

/-- The consumers (valuations in `[0, 1]`) who buy at price `p`: those whose anticipated
utility (2)/(3) is strictly positive (p. 8). -/
def buyers (P : Params) (lam p : ℝ) : Set ℝ :=
  {v | v ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < utility P lam p v}

/-- Demand at price `p`: the `F`-mass of the buyers. -/
noncomputable def demand (P : Params) (F : StieltjesFunction ℝ) (lam p : ℝ) : ℝ :=
  (F.measure (buyers P lam p)).toReal

/-- The firm's profit `(p − c)·D(p)`. -/
noncomputable def profit (P : Params) (F : StieltjesFunction ℝ) (lam p : ℝ) : ℝ :=
  (p - P.c) * demand P F lam p

/-- Consumer welfare (long-run preferences, p. 10): the `F`-integral over the buyers of
their anticipated utility (2)/(3) at the actual usage. -/
noncomputable def consumerWelfare (P : Params) (F : StieltjesFunction ℝ) (lam p : ℝ) : ℝ :=
  ∫ v in buyers P lam p, utility P lam p v ∂F.measure

/-- Social welfare: consumer welfare plus the firm's profit. -/
noncomputable def socialWelfare (P : Params) (F : StieltjesFunction ℝ) (lam p : ℝ) : ℝ :=
  consumerWelfare P F lam p + profit P F lam p

/-- `p` is an optimal price: a nonnegative price maximizing profit over all nonnegative
prices. -/
def IsOptimalPrice (P : Params) (F : StieltjesFunction ℝ) (lam p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ q : ℝ, 0 ≤ q → profit P F lam q ≤ profit P F lam p

/-- `v₁ = (κ − λp)/β` (p. 8). -/
noncomputable def v1 (P : Params) (lam p : ℝ) : ℝ := (P.κ - lam * p) / P.β

/-- `v₂ = (1 − λp)/β` (p. 8). -/
noncomputable def v2 (P : Params) (lam p : ℝ) : ℝ := (1 - lam * p) / P.β

/-- `v₃ = p/α + κ` (p. 8). -/
noncomputable def v3 (P : Params) (p : ℝ) : ℝ := p / P.α + P.κ

/-- `v₄ = p + ακ + (1 − α)` (p. 8). -/
def v4 (P : Params) (p : ℝ) : ℝ := p + P.α * P.κ + (1 - P.α)

/-- `p̂_a = κ(1 − β)α/(λα + β)` (Proposition 1, p. 8). -/
noncomputable def pHatA (P : Params) (lam : ℝ) : ℝ :=
  P.κ * (1 - P.β) * P.α / (lam * P.α + P.β)

/-- `λ₁ = (1 − β)/(α(1 − κ))`, the bound in the hypothesis of Proposition 1 (p. 8). -/
noncomputable def lam1 (P : Params) : ℝ := (1 - P.β) / (P.α * (1 - P.κ))

/-- The objective `(p − c)(1 − F(v₃))` of (7) (p. 10). -/
noncomputable def rProfit (P : Params) (F : StieltjesFunction ℝ) (p : ℝ) : ℝ :=
  (p - P.c) * (1 - F (v3 P p))

end SunkCost.SmallBias


