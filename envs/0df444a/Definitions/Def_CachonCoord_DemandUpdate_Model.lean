-- Prove2me | Definitions.Def_CachonCoord_DemandUpdate_Model
-- name    : CachonCoord_DemandUpdate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:33:36.087767+00:00
-- url     : https://prove2.me/theorems/979490b9-c027-49db-ae1d-cace592bcbec
-- title:
--   §6.6.1, pp. 63–66 — the newsvendor with one forecast update: signal law, conditional demand F(·|ξ), Ω₂ (24) and Ω₁
-- statement:
--   This is the model of the newsvendor with demand updating (Cachon, after Donohue 2000).
--
--   A retailer sells one product at retail price $p$ in a single selling season. Before the season a **demand signal** $\xi \ge 0$ is observed; it has density $g$ on $[0,\infty)$ and distribution function
--   $$G(t) = \int_0^t g(\xi)\,d\xi .$$
--   After observing $\xi$, demand $D$ has distribution function $F(\cdot\,|\,\xi)$. Demand is nonnegative with finite mean, each $F(\cdot\,|\,\xi)$ is continuous and strictly increasing on $[0,\infty)$, and demand is **stochastically increasing** in the signal: $F(x\,|\,\xi_h) < F(x\,|\,\xi_l)$ whenever $\xi_h > \xi_l \ge 0$ and $x > 0$. Expected sales given the signal are $S(q\,|\,\xi) = E[\min(q, D)\,|\,\xi]$, and $E[h(\xi)] = \int_0^\infty h(\xi) g(\xi)\,d\xi$ is the expectation over the signal.
--
--   Period 1 is before the signal, period 2 between the signal and the season. The supplier's unit production cost in period $i$ is $c_i$, with $c_1 < c_2$, and $0 < c_2 < p$. Salvage value and lost-sales costs are zero. If the retailer's total order is $q_1$ after period 1 and $q_2 \ge q_1$ after period 2, the supply chain's expected revenue minus period-2 production cost is (Eq. (24))
--   $$\Omega_2(q_2\,|\,q_1,\xi) = pS(q_2\,|\,\xi) - c_2 q_2 + c_2 q_1 .$$
--   A function $q_2(q_1,\xi)$ is a supply chain optimal period-2 order if, for all $q_1 \ge 0$ and $\xi \ge 0$, it maximizes $\Omega_2(\cdot\,|\,q_1,\xi)$ over $q_2 \ge q_1$. The supply chain's expected profit as a function of the period-1 order is
--   $$\Omega_1(q_1) = -c_1 q_1 + E\big[\Omega_2(q_2(q_1,\xi)\,|\,q_1,\xi)\big].$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The conditional law is a measurable family $\xi \mapsto D_\xi$ of probability measures on $\mathbb R$ (a Markov kernel); measurability and a finite unconditional mean $\int_0^\infty E[D\,|\,\xi]\, g(\xi)\,d\xi < \infty$ are regularity added so that expectations over the signal are genuine integrals. Continuity and strict increase of $F(\cdot\,|\,\xi)$ on $[0,\infty)$ are the chapter's standing assumption (p. 7). The stochastic order is stated for $x > 0$, because both sides vanish at $x \le 0$. The bounds $0 < c_2 < p$ put the critical ratio $(p - c_2)/p$ of (25) in $(0,1)$. $S$ is the platform's `SupplyChainTheory.expSales` applied to the conditional law. $\Omega_1$ takes the selection $q_2(q_1,\xi)$ as an argument; every maximizer gives the same value of $\Omega_2$, so $\Omega_1$ does not depend on the choice.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, pp. 63–64 (model), Eq. (24), p. 64, and the display of Ω₁, p. 66

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

/-- Cachon (2003), 3rd draft (Jan. 2003), §6.6.1, pp. 63–64: the newsvendor with one forecast
update (after Donohue 2000).

* `D ξ` is the law of demand after the demand signal `ξ ≥ 0` is observed; its distribution
  function `F(x|ξ)` is `cdf (D ξ) x`. Demand is nonnegative, has a finite mean, and (the
  chapter's standing assumption, p. 7) `F(·|ξ)` is continuous and strictly increasing on `[0, ∞)`.
* Demand is stochastically increasing in the signal (p. 63): `F(x|ξ_h) < F(x|ξ_l)` for
  `ξ_h > ξ_l` (stated for `x > 0`; at `x ≤ 0` both sides are `0`).
* `ξ ↦ D ξ` is measurable (a Markov kernel), so expectations over the signal make sense.
* The signal has density `g` on `[0, ∞)` (page's `g(·)`), and demand has a finite
  unconditional mean `∫ E[D|ξ] g(ξ) dξ < ∞`.
* `p` is the retail price, `c1 < c2` the supplier's unit production costs in periods 1 and 2
  (page's `c_1, c_2`); `0 < c2 < p` makes the critical ratio `(p − c_2)/p` of (25) lie in `(0, 1)`.
  Salvage value and lost-sales costs are normalized to zero (p. 64). -/
structure Model where
  /-- Conditional demand law given the signal `ξ`. -/
  D : ℝ → Measure ℝ
  isProb : ∀ ξ, 0 ≤ ξ → IsProbabilityMeasure (D ξ)
  nonneg : ∀ ξ, 0 ≤ ξ → D ξ (Set.Iio 0) = 0
  integrable : ∀ ξ, 0 ≤ ξ → Integrable (fun x : ℝ => x) (D ξ)
  continuous_cdf : ∀ ξ, 0 ≤ ξ → Continuous (cdf (D ξ))
  strictMono_cdf : ∀ ξ, 0 ≤ ξ → StrictMonoOn (cdf (D ξ)) (Set.Ici 0)
  /-- Demand is stochastically increasing in the demand signal (p. 63). -/
  stoch_incr : ∀ ξl ξh x : ℝ, 0 ≤ ξl → ξl < ξh → 0 < x → cdf (D ξh) x < cdf (D ξl) x
  measurable_D : Measurable D
  /-- Density `g` of the demand signal on `[0, ∞)`. -/
  g : ℝ → ℝ
  g_measurable : Measurable g
  g_nonneg : ∀ ξ, 0 ≤ g ξ
  g_integrable : IntegrableOn g (Set.Ici 0)
  g_total : ∫ ξ in Set.Ici (0 : ℝ), g ξ = 1
  /-- Finite unconditional mean demand. -/
  mean_integrable : IntegrableOn (fun ξ => (∫ x, x ∂(D ξ)) * g ξ) (Set.Ici 0)
  /-- Retail price `p`. -/
  p : ℝ
  /-- Period-1 unit production cost `c_1`. -/
  c1 : ℝ
  /-- Period-2 unit production cost `c_2`. -/
  c2 : ℝ
  c1_lt_c2 : c1 < c2
  c2_pos : 0 < c2
  c2_lt_p : c2 < p

namespace Model

variable (M : Model)

/-- The conditional demand distribution function `F(x|ξ)`. -/
noncomputable def F (ξ x : ℝ) : ℝ := cdf (M.D ξ) x

/-- Conditional expected sales `S(q|ξ) = E[min(q, D) | ξ]` (§6.2, p. 10, with the law `F(·|ξ)`). -/
noncomputable def S (ξ q : ℝ) : ℝ := SupplyChainTheory.expSales (M.D ξ) q

/-- The signal's distribution function `G(t) = ∫_0^t g(ξ) dξ`. -/
noncomputable def G (t : ℝ) : ℝ := ∫ ξ in Set.Icc 0 t, M.g ξ

/-- Expectation over the signal: `E[h(ξ)] = ∫_0^∞ h(ξ) g(ξ) dξ`. -/
noncomputable def E (h : ℝ → ℝ) : ℝ := ∫ ξ in Set.Ici (0 : ℝ), h ξ * M.g ξ

/-- The critical ratio `(p − c_2)/p` of (25)–(26). -/
noncomputable def ratio : ℝ := (M.p - M.c2) / M.p

/-- Eq. (24), p. 64: the supply chain's expected revenue minus the period-2 production cost,
`Ω_2(q_2|q_1, ξ) = pS(q_2|ξ) − c_2 q_2 + c_2 q_1`. -/
noncomputable def Omega2 (q1 ξ q2 : ℝ) : ℝ := M.p * M.S ξ q2 - M.c2 * q2 + M.c2 * q1

/-- `q2sel q1 ξ` is a supply-chain optimal total order `q_2(q_1, ξ)` (p. 64): for every
`q_1 ≥ 0` and signal `ξ ≥ 0` it maximizes `Ω_2(·|q_1, ξ)` over `q_2 ≥ q_1` (period-1 stock
cannot be returned). -/
def IsChainPeriod2Optimal (q2sel : ℝ → ℝ → ℝ) : Prop :=
  ∀ q1 ξ : ℝ, 0 ≤ q1 → 0 ≤ ξ →
    q1 ≤ q2sel q1 ξ ∧ IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) (q2sel q1 ξ)

/-- p. 66: the supply chain's expected profit `Ω_1(q_1) = −c_1 q_1 + E[Ω_2(q_2(q_1, ξ)|q_1, ξ)]`,
for a selection `q2sel` of the period-2 optimum `q_2(q_1, ξ)`. -/
noncomputable def Omega1 (q2sel : ℝ → ℝ → ℝ) (q1 : ℝ) : ℝ :=
  -M.c1 * q1 + M.E (fun ξ => M.Omega2 q1 ξ (q2sel q1 ξ))

end Model

end CachonCoord.DemandUpdate


