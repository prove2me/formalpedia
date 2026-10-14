-- Prove2me | Definitions.Def_DoubleMoralHazard_Baseline_Arrivals
-- name    : DoubleMoralHazard_Baseline_Arrivals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:27.151467+00:00
-- url     : https://prove2.me/theorems/696008c0-9029-4dcc-aacf-5d3e39ea40c3
-- title:
--   §2.1, pp. 10–11, footnote 8 — arrival process with effort-dependent intensity, channel marks, agent strategies (effort and reporting)
-- statement:
--   This file builds the customer arrival process of the baseline model together with the agent's strategies.
--
--   **Primitives.** The sample space carries an i.i.d. sequence of pairs $(\varepsilon_k,m_k)_{k\ge 0}$ with $\varepsilon_k\sim\mathrm{Exp}(1)$ independent of the channel mark $m_k\sim\mathrm{Bernoulli}(p)$ ($m_k=\text{true}$ means the unobservable channel $u$).
--
--   **Strategies.** A history is the chronological list of arrivals so far, each with its time, its channel and whether it was reported. An agent strategy consists of an effort rule, giving for each history and each later time $t$ whether the agent exerts effort ($\nu_t=\mu$) or not ($\nu_t=0$), and a reporting rule, giving for each history and the time of a new $u$-arrival whether that arrival is reported. Arrivals of channel $o$ are always observed by the principal; a $u$-arrival can be hidden but never invented, so the reported count $\hat N^u$ grows by at most the true count $N^u$. The strategy $\bar\nu$ with truthful reporting always works and reports everything.
--
--   **Arrivals.** After the $k$-th arrival at time $T_k$ (with $T_0=0$) and history $h_k$, the next arrival occurs at the first time $t\ge T_k$ with
--   $$\mu\int_{T_k}^{t}\mathbb 1[\text{effort}(h_k,s)]\,ds\ \ge\ \varepsilon_k,$$
--   or never if no such time exists; its channel is $m_k$. Under this construction the arrival intensity at time $t$ is $\nu_t=\mu\,\mathbb 1[\text{effort}]$, split $p:(1-p)$ between the channels, and under full effort $N^u$ and $N^o$ are independent Poisson processes with rates $p\mu$ and $(1-p)\mu$, as on p. 10. The file also defines the number of arrivals in $[0,t]$ and in $[0,t)$, the realized effort process (which uses only the arrivals strictly before $t$, hence is predictable), and measurability of a strategy.
--
--   **Formalization Note** Effort and reporting are functions of the agent's arrival history, which is the general form of a predictable (resp. adapted) process for the filtration of a marked point process; arrivals cannot occur while the agent shirks, as $\nu_t=0$ requires. A strategy is called measurable when its effort rules are measurable in time and the induced arrival times, observation flags and effort process are measurable. On the null event of infinitely many arrivals in finite time the arrival counts (`Set.ncard`) take the junk value $0$.
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), pp. 10–11, §2.1 and footnote 8; p. 47, proof of Lemma 2 ("the agent cannot over-report cash flows")

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params

namespace DoubleMoralHazard.Baseline

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The sample space. Coordinate `k` carries the clock `ε_k` and the channel mark `m_k` of the
`(k + 1)`-st customer arrival (`m_k = true`: the unobservable channel `u`; `false`: the observable
channel `o`). -/
abbrev Omega : Type := ℕ → ℝ × Bool

/-- The standard exponential law `Exp(1)` of a clock is a probability measure. -/
instance instIsProbabilityMeasureExpOne : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- Law of a channel mark: `true` (channel `u`) with probability `p`, `false` (channel `o`) with
probability `1 - p`. -/
noncomputable def markLaw (P : Params) : Measure Bool :=
  bernoulliMeasure true false ⟨P.p, P.p_pos.le, P.p_lt_one.le⟩

/-- The law of the primitives: the pairs `(ε_k, m_k)` are i.i.d., `ε_k ∼ Exp(1)` independent of
`m_k ∼ Bernoulli(p)`. -/
noncomputable def law (P : Params) : Measure Omega :=
  Measure.infinitePi (fun _ : ℕ => (expMeasure 1).prod (markLaw P))

/-- The agent's record of the arrivals so far, in chronological order: for each arrival its time,
its channel (`true` = `u`) and whether it was reported to the principal (always `true` for an
`o`-arrival, which the principal observes directly). -/
abbrev AgentHistory : Type := List (ℝ × Bool × Bool)

/-- The principal's record: the observed events in chronological order, each a time and a channel
(`true` = a reported `u`-arrival, `false` = an `o`-arrival). -/
abbrev PubHistory : Type := List (ℝ × Bool)

/-- The public part of the agent's history: the reported `u`-arrivals and all `o`-arrivals. -/
def publicPart (h : AgentHistory) : PubHistory :=
  (h.filter (fun e => !e.2.1 || e.2.2)).map (fun e => (e.1, e.2.1))

/-- An agent strategy, as functions of the arrival history.
* `effort h t`: after the arrivals `h` (and none since), at time `t` the agent exerts effort
  (`ν_t = µ`) iff `effort h t = true`; otherwise `ν_t = 0`. Effort at `t` depends on the arrivals
  strictly before `t` only, so the effort process is predictable.
* `report h t`: a `u`-arrival at time `t` that follows the arrivals `h` is reported iff
  `report h t = true`. Unreported `u`-arrivals are hidden (cash diverted); no arrival can be invented,
  so `N̂ᵘ ≤ Nᵘ` increment by increment. -/
structure Strategy where
  effort : AgentHistory → ℝ → Bool
  report : AgentHistory → ℝ → Bool

/-- `ν̄` with truthful reporting: always exert effort and report every arrival. -/
def sbar : Strategy := ⟨fun _ _ => true, fun _ _ => true⟩

/-- The next arrival after time `a` under the effort schedule `e` and clock `ε`: the first `t ≥ a` at
which `µ ∫ₐᵗ 𝕀[e s] ds` reaches `ε`, or `⊤` if it never does. With `ε ∼ Exp(1)` this is an arrival
with intensity `µ · 𝕀[effort]`. -/
noncomputable def nextArrival (P : Params) (e : ℝ → Bool) (a ε : ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ) (_ : a ≤ t ∧ ε ≤ P.mu * ∫ s in a..t, (if e s then (1 : ℝ) else 0)),
    ENNReal.ofReal t

/-- `run P σ ω k`: the agent's history after `k` arrivals and the time `T_k` of the `k`-th arrival
(`T_0 = 0`; `T_k = ⊤` and the history frozen once no further arrival occurs). The `(k + 1)`-st arrival
uses the clock `ε_k = (ω k).1`, the effort schedule following the first `k` arrivals, and the mark
`m_k = (ω k).2`; a `u`-arrival is reported according to `σ.report`. -/
noncomputable def run (P : Params) (σ : Strategy) (ω : Omega) : ℕ → AgentHistory × ℝ≥0∞
  | 0 => ([], 0)
  | k + 1 =>
    let hT := run P σ ω k
    if hT.2 = ⊤ then (hT.1, ⊤) else
      let T := nextArrival P (σ.effort hT.1) hT.2.toReal (ω k).1
      if T = ⊤ then (hT.1, ⊤) else
        (hT.1 ++ [(T.toReal, (ω k).2, if (ω k).2 then σ.report hT.1 T.toReal else true)], T)

/-- The `(k + 1)`-st arrival `(time, channel, reported)`, if it occurs. -/
noncomputable def arrival (P : Params) (σ : Strategy) (ω : Omega) (k : ℕ) :
    Option (ℝ × Bool × Bool) :=
  (run P σ ω (k + 1)).1[k]?

/-- Number of arrivals in `[0, t]`, `Nᵘ_t + Nᵒ_t`. (On the null event of infinitely many arrivals in
finite time, `Set.ncard` returns `0`.) -/
noncomputable def numArrivals (P : Params) (σ : Strategy) (ω : Omega) (t : ℝ) : ℕ :=
  {k : ℕ | 0 < k ∧ (run P σ ω k).2 ≤ ENNReal.ofReal t}.ncard

/-- Number of arrivals in `[0, t)`. -/
noncomputable def numArrivalsBefore (P : Params) (σ : Strategy) (ω : Omega) (t : ℝ) : ℕ :=
  {k : ℕ | 0 < k ∧ (run P σ ω k).2 < ENNReal.ofReal t}.ncard

/-- The realized effort at time `t`: `true` iff `ν_t = µ`. It uses the arrivals strictly before `t`. -/
noncomputable def effortAt (P : Params) (σ : Strategy) (ω : Omega) (t : ℝ) : Bool :=
  σ.effort (run P σ ω (numArrivalsBefore P σ ω t)).1 t

/-- Whether the `(k + 1)`-st arrival is observed by the principal (`true` if it does not occur). -/
noncomputable def observedFlag (P : Params) (σ : Strategy) (ω : Omega) (k : ℕ) : Bool :=
  ((arrival P σ ω k).map (fun e => !e.2.1 || e.2.2)).getD true

/-- A strategy is measurable when its effort schedules are measurable in time and the processes it
induces (arrival times, observation flags, effort) are measurable. -/
def IsMeasurableStrategy (P : Params) (σ : Strategy) : Prop :=
  (∀ h, Measurable (σ.effort h)) ∧
  Measurable (fun q : Omega × ℝ => effortAt P σ q.1 q.2) ∧
  ∀ k, Measurable (fun ω => (run P σ ω k).2) ∧ Measurable (fun ω => observedFlag P σ ω k)

end DoubleMoralHazard.Baseline


