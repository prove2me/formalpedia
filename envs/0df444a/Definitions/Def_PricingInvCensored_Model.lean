-- Prove2me | Definitions.Def_PricingInvCensored_Model
-- name    : PricingInvCensored_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:26.174056+00:00
-- url     : https://prove2.me/theorems/a40b7d35-c0c1-442c-9902-313e5e366f5f
-- title:
--   The joint pricing–inventory instance with censored demand: Assumption 1, $G(p)=\max_y Q(p,y)$, Assumption 2, nonnegative demand
-- statement:
--   **The instance** (§2.1, pp. 4–6). A firm sells one product over periods $t=1,2,\dots$. In each period it posts a price $p_t\in[\underline p,\overline p]$ and raises its stock to a level $y_t$. Demand is $D_t=\lambda(p_t)+\varepsilon_t$, where $\lambda$ is the demand-price curve and the noise $\varepsilon_t$ is drawn i.i.d. from a law $\mu$ with density $f_\mu$ and cumulative distribution function $F_\mu$. Unmet demand is lost at a per-unit penalty $b$ and leftover stock costs $h$ per unit. The expected one-period profit is Eq. (3),
--   $$Q(p,y)=p\lambda(p)-(b+p)\,\mathbb E_\mu[(\lambda(p)+\varepsilon-y)^+]-h\,\mathbb E_\mu[(y-\lambda(p)-\varepsilon)^+],$$
--   taken from the published model `ChenChaoShiSALA_Regret_Model` (whose `Market` stores $\underline p,\overline p,b,h,\lambda,\mu$). The instance adds the constants $\bar y,\underline d,\overline d,\Lambda,\kappa,K,s,S$ and the density $f_\mu$.
--
--   The module defines:
--   1. **Assumption 1** (p. 9) for a clairvoyant pair $(p^*,y^*)$: $\lambda$ maps $[\underline p,\overline p]$ bijectively onto $[\underline d,\overline d]$ with $0\le\underline p<\overline p$ and $0\le\underline d<\overline d$, is strictly decreasing, twice continuously differentiable on $(\underline p,\overline p)$ with $|\lambda'|,|\lambda''|\le\Lambda$; $(p^*,y^*)$ maximizes $Q$ over $[\underline p,\overline p]\times\mathbb R$ with $p^*\in(\underline p,\overline p)$ and $y^*\in(0,\bar y)$; $\mu$ is a probability measure with compact support, mean $0$ and density $f_\mu\ge 0$, and for every $u$ with $\phi(\underline p)\le F_\mu(u)\le\phi(\overline p)$, where $\phi(p)=\frac{b+p}{b+p+h}$,
--   $$0<\kappa\le f_\mu(u)\le K,\qquad |f_\mu'(u)|\le K,\qquad \kappa\le 1\le K;$$
--   and $b\ge 0$, $h>0$.
--   2. The **inventory-optimized profit** $G(p)=\max_{y}Q(p,y)$ (p. 6), as the supremum over all real $y$.
--   3. **Assumption 2** (p. 11): $G$ is twice continuously differentiable on $[\underline p,\overline p]$ and $s^2\le -G''(p)\le S^2$ there, with $0<s^2\le1\le S^2$.
--   4. **Nonnegative demand**: $\mu((-\infty,-\underline d))=0$, so that $D_t\ge 0$ at every price.
--
--   These are the hypotheses of every theorem of the mission.
--
--   **Formalization Note** The clairvoyant pair is an argument with the maximization property; the regret uses only the optimal value $Q(p^*,y^*)$. "Admits an inverse" is a bijection onto $[\underline d,\overline d]$. Compact support is $\mu(\{|x|>B\})=0$ for some $B$; $\mathbb E_\mu[\varepsilon\mid p]=0$ is $\int x\,d\mu=0$. The density is one fixed function $f$ with $\mu=f\cdot\mathrm{Leb}$, and the band clause is about that function. $s^2$ and $S^2$ are written `s ^ 2`, `S ^ 2` with $s>0$. $G''$ is the second derivative within $[\underline p,\overline p]$. The nonnegative-demand hypothesis corrects the model (with $\varepsilon<-\underline d$ the stock can grow and the regret can be linear) and is kept separate because Proposition 1 does not need it.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), §2.1 pp.4–6 (Eqs. (2)–(3)), Assumption 1 p.9, Assumption 2 p.11

import Mathlib
import Definitions.Def_ChenChaoShiSALA_Regret_Model

open MeasureTheory ProbabilityTheory Set

namespace PricingInvCensored

/-- **Problem instance** of Chen, Wang & Zhou, *Optimal Policies for Dynamic Pricing and Inventory
Control with Nonparametric Censored Demands*, SSRN 3750413 (2022-10-19), §2.1, pp.4–6, and
Assumptions 1–2, pp.9 and 11.

The field `market` is the published `ChenChaoShiSALA.Regret.Market`: the price range
`[p̲, p̄] = [market.low, market.high]`, the lost-sales penalty `b = market.b`, the holding cost
`h = market.h`, the demand-price curve `λ = market.demand` and the noise law `µ = market.noise`.
Its `Market.Q` is Eq. (3), p.6, and its `Market.cdf` is `F_µ(x) = µ((-∞, x])`.

The remaining fields are the paper's constants: the known upper bound `ȳ = ybar` of Assumption 1(2),
the demand bounds `d̲ = dlo`, `d̄ = dhi` and the derivative bound `Λ = Lam` of Assumption 1(1), the
density `f_µ = f` and its bounds `κ = kappa`, `K` of Assumption 1(3), and the curvature constants
`s`, `S` of Assumption 2 (the paper's `s²`, `S²` are `s ^ 2`, `S ^ 2`).

**Formalization Note.** The instance carries no assumptions; they are `Assumption1`, `Assumption2`
and `NonnegDemand`. -/
structure Instance where
  /-- Price range, costs `b, h`, demand curve `λ` and noise law `µ`. -/
  market : ChenChaoShiSALA.Regret.Market
  /-- The known upper bound `ȳ` on the optimal order-up-to level. -/
  ybar : ℝ
  /-- Lower demand bound `d̲`. -/
  dlo : ℝ
  /-- Upper demand bound `d̄`. -/
  dhi : ℝ
  /-- Bound `Λ` on `|λ'|` and `|λ''|`. -/
  Lam : ℝ
  /-- The density `f_µ` of the noise law. -/
  f : ℝ → ℝ
  /-- Lower density bound `κ` on the band. -/
  kappa : ℝ
  /-- Upper bound `K` on the density and its derivative on the band. -/
  K : ℝ
  /-- Curvature lower constant: the paper's `s²` is `s ^ 2`. -/
  s : ℝ
  /-- Curvature upper constant: the paper's `S²` is `S ^ 2`. -/
  S : ℝ

/-- **Assumption 1**, p.9 (Chen, Wang & Zhou, SSRN 3750413), for an instance `I` and a clairvoyant
solution `(pStar, yStar)` (Eq. (2), p.6).

1. `λ` maps `[p̲, p̄]` onto `[d̲, d̄]` bijectively, with `0 ≤ p̲ < p̄` and `0 ≤ d̲ < d̄`; it is
   strictly decreasing, twice continuously differentiable on `(p̲, p̄)`, and `|λ'|, |λ''| ≤ Λ` there.
2. `(pStar, yStar)` maximizes `Q` over `[p̲, p̄] × ℝ` (the clairvoyant solution of Eq. (2)), with
   `pStar ∈ (p̲, p̄)` and `yStar ∈ (0, ȳ)`.
3. `µ` is a probability measure with compact support and mean `0`, it has the density `f_µ ≥ 0`,
   and for every `u` with `φ(p̲) ≤ F_µ(u) ≤ φ(p̄)`, where `φ(p) = (b+p)/(b+p+h)`, the density obeys
   `κ ≤ f_µ(u) ≤ K`, `f_µ` is differentiable at `u` and `|f_µ'(u)| ≤ K`; also `0 < κ ≤ 1 ≤ K`.

**Formalization Note.** "Admits an inverse function `λ⁻¹ : [d̲, d̄] → [p̲, p̄]`" is `Set.BijOn`.
The clairvoyant solution is an argument with the maximization property (any maximizer: the regret
only uses the optimal value `Q(p*, y*)`); the maximization is over all real levels `y` (p.6, "arg
max over p, y"). "Compact support" is `µ({x : B < |x|}) = 0` for some `B`. `E_µ[ε | p] = 0` is
`∫ x dµ = 0` (the noise does not depend on the price). The density is one fixed function `f`
with `µ = f · Lebesgue`; the band clause is about that function. The costs satisfy `0 ≤ b` and
`0 < h` (the paper calls them per-unit costs; `h > 0` is also forced by the band clause together
with compact support). -/
structure Assumption1 (I : Instance) (pStar yStar : ℝ) : Prop where
  low_nonneg : 0 ≤ I.market.low
  low_lt_high : I.market.low < I.market.high
  dlo_nonneg : 0 ≤ I.dlo
  dlo_lt_dhi : I.dlo < I.dhi
  demand_bijOn : BijOn I.market.demand (Icc I.market.low I.market.high) (Icc I.dlo I.dhi)
  demand_strictAntiOn : StrictAntiOn I.market.demand (Icc I.market.low I.market.high)
  demand_contDiffOn : ContDiffOn ℝ 2 I.market.demand (Ioo I.market.low I.market.high)
  deriv_le : ∀ p ∈ Ioo I.market.low I.market.high, |deriv I.market.demand p| ≤ I.Lam
  deriv2_le : ∀ p ∈ Ioo I.market.low I.market.high,
    |deriv (deriv I.market.demand) p| ≤ I.Lam
  clairvoyant_max : ∀ p ∈ Icc I.market.low I.market.high, ∀ y : ℝ,
    I.market.Q p y ≤ I.market.Q pStar yStar
  pStar_mem : pStar ∈ Ioo I.market.low I.market.high
  yStar_mem : yStar ∈ Ioo 0 I.ybar
  b_nonneg : 0 ≤ I.market.b
  h_pos : 0 < I.market.h
  noise_prob : IsProbabilityMeasure I.market.noise
  noise_compact : ∃ B : ℝ, I.market.noise {x : ℝ | B < |x|} = 0
  noise_mean : ∫ x, x ∂I.market.noise = 0
  f_nonneg : ∀ x, 0 ≤ I.f x
  f_measurable : Measurable I.f
  noise_density : I.market.noise = volume.withDensity (fun x => ENNReal.ofReal (I.f x))
  band : ∀ u : ℝ, I.market.quantileLevel I.market.low ≤ I.market.cdf u →
    I.market.cdf u ≤ I.market.quantileLevel I.market.high →
    I.kappa ≤ I.f u ∧ I.f u ≤ I.K ∧ DifferentiableAt ℝ I.f u ∧ |deriv I.f u| ≤ I.K
  kappa_pos : 0 < I.kappa
  kappa_le_one : I.kappa ≤ 1
  one_le_K : 1 ≤ I.K

/-- The inventory-optimized expected profit `G(p) := max_y Q(p, y)`, p.6 (Chen, Wang & Zhou,
SSRN 3750413).

**Formalization Note.** The maximum is over all real `y` (p.6), written as the supremum
`⨆ y : ℝ, Q(p, y)`. Under Assumption 1 the maximum is attained (Proposition 1, Item 2), so the
real supremum is the paper's maximum. -/
noncomputable def G (I : Instance) (p : ℝ) : ℝ := ⨆ y : ℝ, I.market.Q p y

/-- **Assumption 2 (Concavity of G)**, p.11 (Chen, Wang & Zhou, SSRN 3750413): `G` is twice
continuously differentiable and `s² ≤ −G''(p) ≤ S²` for all `p ∈ [p̲, p̄]`, with
`0 < s² ≤ 1 ≤ S² < ∞`.

**Formalization Note.** Differentiability is on the closed interval `[p̲, p̄]` (`ContDiffOn`), and
`G''` is the second derivative within `[p̲, p̄]` (`iteratedDerivWithin 2`), so the endpoints are
included as printed. The paper's `s²` is `s ^ 2` with `0 < s` (the sign of `s` is immaterial;
only `s²` enters). -/
structure Assumption2 (I : Instance) : Prop where
  s_pos : 0 < I.s
  s_sq_le_one : I.s ^ 2 ≤ 1
  one_le_S_sq : 1 ≤ I.S ^ 2
  G_contDiffOn : ContDiffOn ℝ 2 (G I) (Icc I.market.low I.market.high)
  curvature : ∀ p ∈ Icc I.market.low I.market.high,
    I.s ^ 2 ≤ -iteratedDerivWithin 2 (G I) (Icc I.market.low I.market.high) p ∧
      -iteratedDerivWithin 2 (G I) (Icc I.market.low I.market.high) p ≤ I.S ^ 2

/-- **Nonnegative demand** (a correction of Chen, Wang & Zhou, SSRN 3750413, §2.1, p.5): the noise
puts no mass below `−d̲`, so the demand `D_t = λ(p_t) + ε_t ≥ λ(p_t) − d̲ ≥ 0` almost surely at
every price in `[p̲, p̄]`.

**Formalization Note.** The paper's model speaks of quantities (orders, sales `min{D_t, y_t}`, lost
sales `(D_t − y_t)⁺`) but does not exclude `ε_t < −d̲`; with negative demand the stock can grow
(`x_{t+1} = y_t − D_t > y_t`) and the regret can be linear. This hypothesis is kept apart from
`Assumption1` because Proposition 1 does not use it. -/
def NonnegDemand (I : Instance) : Prop := I.market.noise (Iio (-I.dlo)) = 0

end PricingInvCensored


