-- Prove2me | Definitions.Def_ObsArrivalPricing_PeriodicPolicy
-- name    : ObsArrivalPricing_PeriodicPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:51.148149+00:00
-- url     : https://prove2.me/theorems/024dbab7-d88a-4205-8798-769475d3a2fb
-- title:
--   The periodic policy $\hat p$ of (4), its random shift and $R^{uo}_\tau$
-- statement:
--   Fix $T>0$ and a price function $p$. Every time $t$ has a **phase** $s\in(0,2T]$, its representative modulo $2T$. The periodic policy of (4) is
--   $$\hat p(t)=\begin{cases}p(0)&s\in(0,T]\quad(t\in I_{2k-1}=(2(k-1)T,(2k-1)T]),\\ p(s-T)&s\in(T,2T)\quad(t\in I_{2k}),\\ \min(p(0),p(T))&s=2T.\end{cases}$$
--   On the "blocks" $I_{2k-1}$ the price is held at $p(0)$, so that arriving buyers accumulate; on $I_{2k}$ the policy replays $p$ on $[0,T]$. The randomly shifted policy is $\hat p_{t_0}(t)=\hat p(t+t_0)$, and for an arrival time $\tau$
--   $$R^{uo}_\tau=\frac1{2T}\int_0^{2T}\int \text{revenue of }\hat p_{t_0}\text{ from a buyer }(\tau,v)\,dF(v)\,dt_0,$$
--   the seller's expected revenue in the unobservable case when the buyer arrives at $\tau$ and $t_0\sim\mathrm{Unif}[0,2T]$.
--
--   This is the feasible unobservable policy through which the paper bounds the value of observability.
--
--   **Formalization Note** At the junction points $t=2kT$ (4) gives $p(T)$; the value here is $\min(p(0),p(T))$, which agrees with (4) for the paper's non-increasing $p$ and keeps $\hat p$ lower semicontinuous for every admissible $p$. The phase is `toIocMod` with period $2T$; for $T\le0$ it is an unused placeholder. Both integrals in $R^{uo}_\tau$ are lower Lebesgue integrals.
-- source:
--   Correa, Pizarro & Vulcano, The Value of Observing the Buyer Arrival Time in Dynamic Pricing, SSRN 3541494 (rev. Oct 2022), (4), p.18; Proposition 3, p.20; p.23 (definition of R^uo_τ); proof of Lemma 3, pp.A7–A9

import Mathlib
import Definitions.Def_ObsArrivalPricing_Model

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ObsArrivalPricing

/-- The phase of time `t` in a period of length `2T`: the representative of `t` modulo `2T` in
`(0, 2T]` (SSRN 3541494, (4), p.18: `I_{2k−1} = (2(k−1)T, (2k−1)T]`, `I_{2k} = ((2k−1)T, 2kT]`).

**Formalization Note** For `T > 0` this is `toIocMod` with period `2T` and base point `0`; the value
for `T ≤ 0` is an unused placeholder (`t`). -/
noncomputable def phase (T t : ℝ) : ℝ :=
  if h : 0 < T then toIocMod (mul_pos two_pos h) 0 t else t

/-- The periodic price function `p̂` of (4) (SSRN 3541494, p.18):
`p̂(t) = p(0)` for `t ∈ I_{2k−1}` (phase in `(0, T]`, a "block") and `p̂(t) = p(t − (2k−1)T)` for
`t ∈ I_{2k}` (phase `s ∈ (T, 2T)`, where the value is `p(s − T)`).

**Formalization Note** At the junction points `t = 2kT` (phase `2T`), (4) gives `p(T)`; here the
value is `min (p 0) (p T)`, which equals (4) for the paper's non-increasing `p` ("we can assume that
p(t) is nonincreasing", p.11) and keeps `p̂` lower semicontinuous for every admissible `p`. The
periodic rule also defines `p̂` at `t ≤ 0`, which (4) leaves undefined. -/
noncomputable def phat (p : ℝ → ℝ) (T t : ℝ) : ℝ :=
  if phase T t ≤ T then p 0
  else if phase T t < 2 * T then p (phase T t - T)
  else min (p 0) (p T)

/-- The randomly shifted policy `p̂_{t0}(t) = p̂(t + t0)` (SSRN 3541494, Proposition 3, p.20). -/
noncomputable def shiftedPolicy (p : ℝ → ℝ) (T t0 : ℝ) : ℝ → ℝ := fun t => phat p T (t + t0)

/-- `R^uo_τ` for the randomly shifted policy: the seller's expected revenue in the unobservable case
when the buyer's arrival time is `τ`, the shift is `t0 ∼ Unif[0, 2T]` and the valuation is
`v ∼ F` (SSRN 3541494, p.23: "Ruo_τ, which we define as the seller's expected revenue in the
unobservable case when the buyer's arrival time is τ"; Proposition 3, p.20; proof of Lemma 3,
pp.A7–A9).

**Formalization Note** The uniform law on `[0, 2T]` is `(1/(2T))` times Lebesgue measure on
`[0, 2T]`; both integrals are lower Lebesgue integrals (`lintegral`). -/
noncomputable def RuoTau (F : Measure ℝ) (δ μ : ℝ) (p : ℝ → ℝ) (T τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * T)) *
    ∫⁻ t0 in Icc 0 (2 * T), ∫⁻ v, ENNReal.ofReal (rev δ μ (shiftedPolicy p T t0) τ v) ∂F

end ObsArrivalPricing


