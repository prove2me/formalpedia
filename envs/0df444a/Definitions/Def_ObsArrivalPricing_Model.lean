-- Prove2me | Definitions.Def_ObsArrivalPricing_Model
-- name    : ObsArrivalPricing_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:16.613093+00:00
-- url     : https://prove2.me/theorems/4f597922-5310-4032-88ff-093c04c5e428
-- title:
--   Dynamic pricing with one forward-looking buyer: purchase rule, revenues $R$, $R^{uo}$ and the value of observability
-- statement:
--   A seller holds one item and posts a price function $p(t)$, $t\ge 0$. A single buyer arrives at a random time $\tau\sim G$ (possibly never) with a private valuation $v\sim F$ on $[0,\bar v]$, independent of $\tau$. The seller discounts at rate $\delta$ and the buyer at rate $\mu$, with $0\le\delta<\mu$.
--
--   1. **Utility.** Purchasing at time $t$ gives the buyer $U(t,v)=e^{-\mu t}(v-p(t))$; never purchasing gives $U(\infty,v)=0$.
--   2. **Purchase rule.** A buyer arriving at $\tau$ solves $[BP]\ \max_{\tau\le t\le\infty}U(t,v)$ and purchases at the **earliest** maximizer. He purchases at a finite time $t$ exactly when $t\ge\tau$, $U(t,v)\ge 0$, $U(t,v)\ge U(s,v)$ for all $s\ge\tau$, and $U(s,v)<U(t,v)$ for all $s\in[\tau,t)$. The seller then earns $e^{-\delta t}p(t)$, and $0$ if the buyer never purchases.
--   3. **Admissible prices.** $p:[0,\infty)\to[0,\bar v]$ is lower semicontinuous and twice differentiable almost everywhere.
--   4. **Observable case.** With $\mathrm{Rev}_0(p)=\mathbb E_{v\sim F}[\text{revenue from a buyer arriving at }0]$ and $R_{[0,T]}(p)$ the same expectation restricted to purchases at times $\le T$, the optimal value of $[SPO_0]$ is $R_0=\sup_p \mathrm{Rev}_0(p)$ over admissible $p$, and
--   $$R=R_0\int_0^\infty e^{-\delta\tau}\,dG(\tau).$$
--   5. **Unobservable case.** One admissible $p$ is posted from time $0$; $R^{uo}=\sup_p\mathbb E_{\tau\sim G,\,v\sim F}[\text{revenue}]$.
--   6. **Value of observability.** $VO(G,F,\delta,\mu)=R/R^{uo}$ and $VO=\sup_{G,F,\delta,\mu}VO(G,F,\delta,\mu)$.
--   7. **The constant.** With $W_{-1}$ the negative branch of the Lambert function, $w^\star=W_{-1}(-1/(2\sqrt e))$, $c^\star=e^{w^\star+1/2}$, $C=-(2w^\star+1)/(e^{w^\star+1/2}-1)^2$ and $g(c)=2\ln(1/c)/(1-c)^2$.
--
--   These objects carry every statement of the mission: the buyer's best response, the two optimal revenues and their ratio.
--
--   **Formalization Note** Prices are functions $\mathbb R\to\mathbb R$ of which only $t\ge0$ matters; "twice differentiable at $t$" means differentiable on a neighbourhood of $t$ with a differentiable derivative at $t$, for almost every $t>0$. The purchase time is `Option ℝ` (`none` = never). Revenues are lower Lebesgue integrals of nonnegative reals in $[0,\infty]$, and $VO$ is a quotient in $[0,\infty]$ with $0/0=0$. $F$ and $G$ are arbitrary laws: $G$ lives on $[0,\infty)$ with total mass at most $1$, the missing mass being the arrival at $t=\infty$. $R$ is defined by the paper's formula $R_0\int e^{-\delta\tau}dG$ (p.11), and $R^{uo}$ is a supremum over deterministic admissible prices. $W_{-1}$ is the published `ValuePersPricing.Deviation.lambertWm1`.
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), §3, pp.8–13 (model, [BP], [SPO0], R, [SPN], VO); Theorem 1, p.23; endnote 6, p.25

import Mathlib
import Definitions.Def_ValuePersPricing_Deviation_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- The buyer's exponentially discounted utility `U(t, v) = e^{−µt}(v − p(t))` of purchasing at time
`t` with valuation `v` under the price function `p` (Correa, Pizarro & Vulcano, The Value of
Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), §3.1, p.9).
Not purchasing (`t = ∞`) is worth `U(∞, v) = 0`, which is built into `IsPurchase`.

**Formalization Note** A price function is any `p : ℝ → ℝ`; only its values at `t ≥ 0` matter. -/
noncomputable def U (μ : ℝ) (p : ℝ → ℝ) (v t : ℝ) : ℝ := Real.exp (-μ * t) * (v - p t)

/-- `IsPurchase μ p τ v t`: a buyer arriving at `τ` with valuation `v` purchases at the finite time
`t`, i.e. `t` is the **earliest** maximizer of the buyer's problem
`[BP] max_{τ ≤ t ≤ ∞} U(t, v)` with the outside option `U(∞, v) = 0` (SSRN 3541494, §3.1, pp.9–10:
"the buyer purchases the item at the earliest time maximizing his utility").

**Formalization Note** The four clauses say: `t ≥ τ`; `U(t, v) ≥ U(∞, v) = 0`; `U(t, v)` is
maximal over `[τ, ∞)`; and no earlier time in `[τ, t)` attains it. A finite time with utility `0`
is earlier than `∞`, so such a buyer purchases, as on p.9 ("will purchase (at a finite time) if and
only if there exists τp ∈ [τ,∞) such that U(τp,v) ≥ 0"). -/
def IsPurchase (μ : ℝ) (p : ℝ → ℝ) (τ v t : ℝ) : Prop :=
  τ ≤ t ∧ 0 ≤ U μ p v t ∧ (∀ s, τ ≤ s → U μ p v s ≤ U μ p v t) ∧
    (∀ s, τ ≤ s → s < t → U μ p v s < U μ p v t)

/-- The purchase time of a buyer arriving at `τ` with valuation `v` (SSRN 3541494, pp.9–10):
`some t` when the earliest maximizer `t` of [BP] is finite, `none` when the buyer never purchases
(the paper's `τp = ∞`).

**Formalization Note** `IsPurchase` has at most one solution (two earliest maximizers coincide), so
the choice is canonical; existence for admissible prices is the milestone
`buyer_problem_solvable`. -/
noncomputable def purchaseTime (μ : ℝ) (p : ℝ → ℝ) (τ v : ℝ) : Option ℝ :=
  haveI := Classical.propDecidable (∃ t, IsPurchase μ p τ v t)
  if h : ∃ t, IsPurchase μ p τ v t then some (Classical.choose h) else none

/-- The seller's discounted revenue `e^{−δt} p(t)` from a buyer arriving at `τ` with valuation `v`,
who purchases at `t`; `0` if he never purchases (SSRN 3541494, §3, pp.9–12: "the discounted revenue
for the seller is e^{−δt}p(t)"). -/
noncomputable def rev (δ μ : ℝ) (p : ℝ → ℝ) (τ v : ℝ) : ℝ :=
  match purchaseTime μ p τ v with
  | some t => Real.exp (-δ * t) * p t
  | none => 0

/-- The seller's revenue up to time `T` from a buyer arriving at `0` with valuation `v`: the revenue
`e^{−δt}p(t)` if he purchases at a time `t ≤ T`, else `0`. Integrated against `F` this is
`R_{[0,T]} = p(0)(1 − F(ψ(0))) + ∫_0^T e^{−δt} p(t) d(1 − F(ψ(t)))` (SSRN 3541494, Lemma 1, p.18). -/
noncomputable def revUpTo (δ μ : ℝ) (p : ℝ → ℝ) (T v : ℝ) : ℝ :=
  match purchaseTime μ p 0 v with
  | some t => if t ≤ T then Real.exp (-δ * t) * p t else 0
  | none => 0

/-- Admissible price functions (SSRN 3541494, §3, p.9): `p : [0,∞) → [0, v̄]` "lower
semi-continuous and twice differentiable almost everywhere"; the same class is used "in both cases"
(observable and unobservable).

**Formalization Note** Lower semicontinuity is relative to `[0, ∞)`. "Twice differentiable at `t`"
means `p` is differentiable on a neighbourhood of `t` and `deriv p` is differentiable at `t`; this
holds for Lebesgue-almost every `t > 0`. Values at `t < 0` are unconstrained and never used. No
continuity or monotonicity is required; `p ≡ 0` is admissible. -/
def IsAdmissible (vbar : ℝ) (p : ℝ → ℝ) : Prop :=
  LowerSemicontinuousOn p (Ici 0) ∧ (∀ t, 0 ≤ t → 0 ≤ p t ∧ p t ≤ vbar) ∧
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∃ N ∈ 𝓝 t, DifferentiableOn ℝ p N ∧ DifferentiableAt ℝ (deriv p) t

/-- The observable-case objective of `[SPO0]` for the price function `p`: the expected revenue
from a buyer arriving at time `0` with valuation `v ∼ F` (SSRN 3541494, §3.2.1, p.11). -/
noncomputable def Rev0 (F : Measure ℝ) (δ μ : ℝ) (p : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (rev δ μ p 0 v) ∂F

/-- The expected revenue `R_{[0,T]}` collected up to time `T` from a buyer arriving at time `0`
(SSRN 3541494, Lemma 1, p.18). -/
noncomputable def RevUpTo (F : Measure ℝ) (δ μ : ℝ) (p : ℝ → ℝ) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (revUpTo δ μ p T v) ∂F

/-- `R0`, the optimal value of `[SPO0]` (SSRN 3541494, §3.2.1, p.11): the supremum of `Rev0` over
admissible price functions. No optimal price is assumed to exist. -/
noncomputable def R0 (vbar : ℝ) (F : Measure ℝ) (δ μ : ℝ) : ℝ≥0∞ :=
  ⨆ (p : ℝ → ℝ) (_ : IsAdmissible vbar p), Rev0 F δ μ p

/-- The unobservable-case objective of `[SPN]` for the price function `p` posted from time `0`:
the expected revenue when the arrival time is `τ ∼ G` and the valuation is `v ∼ F`, independent
(SSRN 3541494, §3.2.2, p.12).

**Formalization Note** The paper writes `[SPN]` through the threshold `φ` "under the assumption of
`p` being continuous" ("just for simplicity", p.12); this primitive form is the same quantity and
is defined for every admissible `p`. Both integrals are lower Lebesgue integrals (`lintegral`). -/
noncomputable def RevUO (F G : Measure ℝ) (δ μ : ℝ) (p : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ τ, ∫⁻ v, ENNReal.ofReal (rev δ μ p τ v) ∂F ∂G

/-- A problem instance `(G, F, δ, µ)` of the value of observability (SSRN 3541494, §3, p.8 and
§3.3.1, p.13): a valuation law `F` on `[0, v̄]`, an arrival-time law `G` on `[0, ∞)` and discount
rates `0 ≤ δ < µ`.

**Formalization Note** `F` and `G` are arbitrary laws (atoms allowed) instead of densities. `G` has
total mass at most `1`; the missing mass `1 − G(ℝ)` is the paper's arrival at `t = ∞` ("the
consumer may never arrive", p.8). `δ = 0` is allowed (the paper evaluates `δ = 0`, pp.22–23;
"δ ≥ 0", p.A9). `µ > 0` follows from `0 ≤ δ < µ`. -/
structure ProblemInstance where
  vbar : ℝ
  F : Measure ℝ
  G : Measure ℝ
  δ : ℝ
  μ : ℝ
  vbar_nonneg : 0 ≤ vbar
  F_prob : IsProbabilityMeasure F
  F_supp : F (Icc 0 vbar)ᶜ = 0
  G_supp : G (Iio 0) = 0
  G_mass : G univ ≤ 1
  δ_nonneg : 0 ≤ δ
  δ_lt_μ : δ < μ

/-- The seller's optimal expected revenue in the observable case,
`R = ∫_0^∞ R_τ g(τ) dτ = R0 ∫_0^∞ e^{−δτ} g(τ) dτ` with `R_τ = e^{−δτ} R0`
(SSRN 3541494, §3.2.1, p.11). -/
noncomputable def R (I : ProblemInstance) : ℝ≥0∞ :=
  R0 I.vbar I.F I.δ I.μ * ∫⁻ τ, ENNReal.ofReal (Real.exp (-I.δ * τ)) ∂I.G

/-- `Ruo`, the optimal value of `[SPN]` (SSRN 3541494, §3.2.2, p.12): the supremum of the
unobservable-case revenue over admissible price functions posted from time `0`. -/
noncomputable def Ruo (I : ProblemInstance) : ℝ≥0∞ :=
  ⨆ (p : ℝ → ℝ) (_ : IsAdmissible I.vbar p), RevUO I.F I.G I.δ I.μ p

/-- The instance value of observability `VO(G, F, δ, µ) = R / Ruo` (SSRN 3541494, §3.3.1, p.13).

**Formalization Note** The quotient is taken in `ℝ≥0∞`: `0/0 = 0` (both revenues vanish when the
buyer never arrives) and `x/0 = ⊤` for `x > 0`. -/
noncomputable def VOinst (I : ProblemInstance) : ℝ≥0∞ := R I / Ruo I

/-- The instance-independent value of observability `VO = sup_{G,F,δ,µ} VO(G, F, δ, µ)`
(SSRN 3541494, §3.3.1, p.13), over all instances with `δ < µ`. -/
noncomputable def VO : ℝ≥0∞ := ⨆ I : ProblemInstance, VOinst I

/-- `W₋₁(−1/(2√e))`, the negative branch of the Lambert function (SSRN 3541494, Theorem 1, p.23,
and endnote 6, p.25: "the branch satisfying W(x) ≤ −1"). The argument `−1/(2√e) ≈ −0.3033` lies in
`(−1/e, 0)`. -/
noncomputable def wStar : ℝ :=
  ValuePersPricing.Deviation.lambertWm1 (-1 / (2 * Real.sqrt (Real.exp 1)))

/-- The bound `−(2W₋₁(−1/(2√e)) + 1) / (e^{W₋₁(−1/(2√e)) + 1/2} − 1)²` of Theorem 1
(SSRN 3541494, p.23). -/
noncomputable def voBound : ℝ := -(2 * wStar + 1) / (Real.exp (wStar + 1 / 2) - 1) ^ 2

/-- The minimizing constant `c = e^{W₋₁(−1/(2√e)) + 1/2}` (SSRN 3541494, proof of Theorem 1,
p.23). -/
noncomputable def cStar : ℝ := Real.exp (wStar + 1 / 2)

/-- The ratio bound `2 ln(1/c) / (1 − c)²` of the proof of Theorem 1 (SSRN 3541494, p.23). -/
noncomputable def ratioBound (c : ℝ) : ℝ := 2 * Real.log (1 / c) / (1 - c) ^ 2

end ObsArrivalPricing


