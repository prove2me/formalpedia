-- Prove2me | Definitions.Def_EventTimeMeasure_Model
-- name    : EventTimeMeasure_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:03.891108+00:00
-- url     : https://prove2.me/theorems/d240191f-6c86-46eb-9821-ae1984f6ba5f
-- title:
--   Event timing model of §2.1: exponential thresholds, hazard clocks $H^i$, event times $\tau_i$, filtration $\mathbb F$
-- statement:
--   The event timing model of §2.1 (pp.5–6) of Giesecke and Shkolnik.
--
--   On a probability space $(\Omega,\mathcal F,P)$, $n$ events are constructed as follows.
--
--   1. **Thresholds.** $\xi_1,\dots,\xi_n$ are standard exponential random variables.
--   2. **Clocks.** For each $i$, $\mathbb H_i=(\mathcal H^i_s)_{s\ge0}$ is a right-continuous filtration and $h^i\ge0$ is an $\mathbb H_i$-progressively measurable hazard rate, with clock
--   $$H^i_t=\int_0^t h^i_s\,ds \qquad (3)$$
--   finite for every finite $t$ and $H^i_\infty=\infty$, almost surely.
--   3. **Event times and indicators.**
--   $$\tau_i=\inf\{t>0: H^i_t\ge\xi_i\}\quad(2),\qquad N^i_s=\mathbf 1\{\tau_i\le s\}\quad(1),\qquad p^i_s=h^i_s\mathbf 1\{\tau_i>s\}.$$
--   4. **Information.** $\mathbb F=(\mathcal F_s)_{s\ge0}$ is a right-continuous filtration containing every $\mathbb H_i$, for which every $\tau_i$ is a stopping time. $\mathcal H^i_\infty=\bigvee_t\mathcal H^i_t$.
--
--   The bundle also defines the two conditions under which the corrected Theorem 3.1 holds.
--
--   - **Sequential independence.** For every $i$, $\xi_i$ is independent of $\sigma(\mathcal H^j_\infty: j\le i)\vee\sigma(\xi_j: j<i)$. It implies the two independence assumptions printed on p.5 (the $\xi_i$ are mutually independent; $\mathcal H^i_\infty$ is independent of $\sigma(\xi_i)$) and equals them for $n=1$.
--   - **Compensator hypothesis.** For every $i$, $M^i=N^i-H^i_{\cdot\wedge\tau_i}$ is an $\mathbb F$-martingale under $P$. The paper asserts this on p.5 as a consequence of the setting; it is an assumption here.
--
--   This is the model every statement of the mission is about; the change of measure is defined on top of it.
--
--   **Formalization Note** Time is $[0,\infty)$ (`ℝ≥0`) and event times take values in $[0,\infty]$ (`WithTop ℝ≥0`), so $\inf\emptyset=\infty$. Clocks are lower Lebesgue integrals with values in $[0,\infty]$, evaluated at any time in $[0,\infty]$; continuity, monotonicity and $H^i_0=0$ follow from the integral form. The paper's $\mathbb F$ is the progressive enlargement of $\mathbb H_1\vee\dots\vee\mathbb H_n$ (fn 7); here any right-continuous $\mathbb F$ with the listed properties is allowed. Completeness, total inaccessibility and almost-sure distinctness of the $\tau_i$ (p.5) are not assumed; under sequential independence the $\tau_i$ are almost surely distinct anyway. Mathlib's `Martingale` omits integrability, so the compensator hypothesis states it separately.
-- source:
--   Giesecke–Shkolnik, Reducing Bias in Event Time Simulations via Measure Changes, authors' manuscript of January 16, 2018 (Math. Oper. Res., doi:10.1287/moor.2021.1156), §2.1, pp.5–6, eqs. (1)–(3), fn 7; corrections 1–2 of Theorem 3.1, p.9

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace EventTimeMeasure

/-- **Lebesgue measure on the time axis `[0, ∞)`** (Giesecke–Shkolnik, *Reducing Bias in Event
Time Simulations via Measure Changes*, manuscript of January 16, 2018, §2.1, eq. (3), p.6: the
`ds` of `H^i_t = ∫_0^t h^i_s ds`).

**Formalization Note** Time is `ℝ≥0`; the measure is the pull-back of Lebesgue measure on `ℝ`
along the inclusion `ℝ≥0 → ℝ`. -/
noncomputable def leb : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

/-- **Integrated rate (clock)** (Giesecke–Shkolnik, manuscript of January 16, 2018, eq. (3),
p.6, and eq. (7), p.9): for a nonnegative rate process `r`, a time `t ∈ [0, ∞]` and an outcome
`ω`, `∫_0^t r_s(ω) ds`.

**Formalization Note** The time argument lives in `WithTop ℝ≥0`, so that the same function gives
the clock at a finite time `t`, at a random time such as `τ_i`, and at `t = ∞`
(`H^i_∞ = ∫_0^∞ h^i_s ds`). The integral is a lower Lebesgue integral with values in `ℝ≥0∞`; it is
never a junk value, and it is `∞` exactly when the rate is not integrable on `[0, t]`. -/
noncomputable def clock {Ω : Type*} (r : ℝ≥0 → Ω → ℝ≥0) (t : WithTop ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ t}, (r s ω : ℝ≥0∞) ∂leb

/-- **Event time** (Giesecke–Shkolnik, manuscript of January 16, 2018, eq. (2), p.5):
`τ = inf {t > 0 : H_t ≥ ξ}` with `H_t = ∫_0^t r_s ds`.

**Formalization Note** The infimum is taken in `WithTop ℝ≥0 = [0, ∞]`, so `inf ∅ = ∞`: an event
whose clock never reaches its threshold has `τ = ∞` (not the junk value `0` of a real `sInf`).
The threshold `ξ` is real-valued and enters through `ENNReal.ofReal`; it is a standard
exponential, so `ξ > 0` almost surely. -/
noncomputable def eventTime {Ω : Type*} (ξ : Ω → ℝ) (r : ℝ≥0 → Ω → ℝ≥0) (ω : Ω) :
    WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ s : ℝ≥0, t = s ∧ 0 < s ∧ ENNReal.ofReal (ξ ω) ≤ clock r s ω}

/-- **Event indicator process** (Giesecke–Shkolnik, manuscript of January 16, 2018, eq. (1),
p.5): `N_s = 1{τ ≤ s}` for `s ≥ 0`. -/
noncomputable def indicatorProcess {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if τ ω ≤ (s : WithTop ℝ≥0) then 1 else 0

/-- **Event timing model** (Giesecke–Shkolnik, manuscript of January 16, 2018, §2.1, pp.5–6,
eqs. (1)–(3)). On a probability space `(Ω, 𝓕, P)`, `n` events, indexed by `Fin n`, are built as
follows.

1. Thresholds `ξ_1, …, ξ_n`: measurable, each standard exponential (`P ∘ ξ_i⁻¹ = Exp(1)`).
2. For each `i` a right-continuous filtration `ℍ_i = (𝓗^i_s)_{s ≥ 0}` and a nonnegative
   `ℍ_i`-progressively measurable hazard rate `h^i`, whose clock `H^i_t = ∫_0^t h^i_s ds` (3) is
   finite at every finite `t` and satisfies `H^i_∞ = ∞`, almost surely.
3. Event times `τ_i = inf{t > 0 : H^i_t ≥ ξ_i}` (2).
4. A right-continuous filtration `𝔽` containing every `ℍ_i`, for which every `τ_i` is a
   stopping time.

The independence requirements of p.5 are *not* part of this structure: the corrected Theorem 3.1
replaces them by `Model.SeqIndep`, which implies both of them.

**Formalization Note** Time is `ℝ≥0`, event times take values in `WithTop ℝ≥0`. "`H^i` is
continuous, increasing, `ℍ_i`-adapted, `H^i_0 = 0`" is not a separate field: it follows from the
integral form (3) with a progressively measurable `h^i` and the finiteness field. The paper takes
`𝔽` to be the progressive enlargement of `ℍ_1 ∨ ⋯ ∨ ℍ_n` by the `τ_i` (fn 7); here `𝔽` is any
right-continuous filtration containing the `ℍ_i` that makes the `τ_i` stopping times. Completeness
of the space and of the filtrations, and total inaccessibility of the `τ_i`, are not assumed.
Almost-sure distinctness of the `τ_i` (p.5) is not a field: under `Model.SeqIndep` it follows,
because for `i < j` the atomless `ξ_j` is independent of the value `H^j_{τ_i}` that `τ_j = τ_i`
would force it to take. -/
structure Model {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) where
  /-- The thresholds `ξ_i`. -/
  ξ : Fin n → Ω → ℝ
  measurable_ξ : ∀ i, Measurable (ξ i)
  /-- Each `ξ_i` is a standard exponential random variable. -/
  map_ξ : ∀ i, P.map (ξ i) = expMeasure 1
  /-- The clock filtrations `ℍ_i`. -/
  𝓗 : Fin n → Filtration ℝ≥0 m
  rightCont_𝓗 : ∀ i, (𝓗 i).IsRightContinuous
  /-- The hazard rates `h^i`. -/
  h : Fin n → ℝ≥0 → Ω → ℝ≥0
  progressive_h : ∀ i, IsStronglyProgressive (𝓗 i) (h i)
  /-- `H^i_t < ∞` for every finite `t`, almost surely. -/
  clock_ne_top : ∀ i, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, clock (h i) t ω ≠ ⊤
  /-- `H^i_∞ = ∞` almost surely. -/
  clock_top : ∀ i, ∀ᵐ ω ∂P, clock (h i) ⊤ ω = ⊤
  /-- The information filtration `𝔽`. -/
  𝓕 : Filtration ℝ≥0 m
  rightCont_𝓕 : 𝓕.IsRightContinuous
  𝓗_le_𝓕 : ∀ i, 𝓗 i ≤ 𝓕
  isStoppingTime : ∀ i, IsStoppingTime 𝓕 (eventTime (ξ i) (h i))

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

/-- The event time `τ_i = inf{t > 0 : H^i_t ≥ ξ_i}` of event `i` (eq. (2), p.5). -/
noncomputable def τ (M : Model P n) (i : Fin n) : Ω → WithTop ℝ≥0 := eventTime (M.ξ i) (M.h i)

/-- The event indicator `N^i_s = 1{τ_i ≤ s}` (eq. (1), p.5). -/
noncomputable def N (M : Model P n) (i : Fin n) : ℝ≥0 → Ω → ℝ := indicatorProcess (M.τ i)

/-- The clock `H^i_t = ∫_0^t h^i_s ds`, `t ∈ [0, ∞]` (eq. (3), p.6). -/
noncomputable def H (M : Model P n) (i : Fin n) : WithTop ℝ≥0 → Ω → ℝ≥0∞ := clock (M.h i)

/-- The intensity `p^i_s = h^i_s 1{τ_i > s}` (p.6). -/
noncomputable def p (M : Model P n) (i : Fin n) (s : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if (s : WithTop ℝ≥0) < M.τ i ω then M.h i s ω else 0

/-- The terminal σ-algebra `𝓗^i_∞ = ⋁_t 𝓗^i_t` of the clock filtration `ℍ_i` (p.5). -/
@[instance_reducible] def Hinf (M : Model P n) (i : Fin n) : MeasurableSpace Ω := ⨆ t, M.𝓗 i t

/-- **Sequential independence** (correction 1 of Theorem 3.1 of Giesecke–Shkolnik, manuscript of
January 16, 2018; replaces the two independence assumptions of §2.1, p.5). For every `i`, the
threshold `ξ_i` is independent under `P` of `σ(𝓗^j_∞ : j ≤ i) ∨ σ(ξ_j : j < i)`.

It implies that the `ξ_i` are mutually independent and that each `𝓗^i_∞` is independent of
`σ(ξ_i)`, the two printed assumptions; for `n = 1` it is the printed assumption. -/
def SeqIndep (M : Model P n) : Prop :=
  ∀ i : Fin n, Indep (MeasurableSpace.comap (M.ξ i) inferInstance)
    ((⨆ j ≤ i, M.Hinf j) ⊔ (⨆ j < i, MeasurableSpace.comap (M.ξ j) inferInstance)) P

/-- **Compensator hypothesis** (correction 2 of Theorem 3.1 of Giesecke–Shkolnik, manuscript of
January 16, 2018; stated on p.5 as a consequence of the setting). For every `i`,
`M^i_t = N^i_t − H^i_{t ∧ τ_i}` is an `𝔽`-martingale under `P`: adapted, integrable at every time,
and `E(M^i_t | 𝓕_s) = M^i_s` for `s ≤ t`.

**Formalization Note** Mathlib's `Martingale` does not include integrability, so integrability at
every time is a separate conjunct. `H^i_{t ∧ τ_i}` is the clock at the time `min t τ_i ∈ [0, ∞]`,
converted to a real number; it is finite almost surely. -/
def CompensatorMartingale (M : Model P n) : Prop :=
  ∀ i : Fin n,
    Martingale (fun t ω ↦ M.N i t ω - (M.H i (min (t : WithTop ℝ≥0) (M.τ i ω)) ω).toReal) M.𝓕 P ∧
    ∀ t : ℝ≥0, Integrable (fun ω ↦ M.N i t ω - (M.H i (min (t : WithTop ℝ≥0) (M.τ i ω)) ω).toReal) P

end Model

end EventTimeMeasure


