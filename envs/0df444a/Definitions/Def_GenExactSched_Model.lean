-- Prove2me | Definitions.Def_GenExactSched_Model
-- name    : GenExactSched_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:08.99681+00:00
-- url     : https://prove2.me/theorems/eb78609b-fe95-4075-9461-b47017b0d959
-- title:
--   Deadline-scheduling model: rate profiles (14), $\hat\sigma$ (79), extension (90), $P(t)$, $\mathrm{Var}(P)$, penalty rates, policies (4), corrected (25), (96), corrected (26)
-- statement:
--   This module defines the stationary deadline-scheduling model of Nakahira, Ferragut and Wierman.
--
--   **Jobs and arrivals** (§2, §3.1). A job is $(a;\sigma,\tau)$: arrival time $a$, service demand $\sigma$, sojourn time $\tau$, so its deadline is $a+\tau$. The job types lie in a measurable bounded set $S\subseteq\{0\le\sigma\le\tau\}$ and have a probability law $\mu$ carried by $S$ (`MarkAssumptions`). Jobs arrive as a Poisson random measure $N$ on $\mathbb R\times\mathbb R^2$ with intensity $\Lambda\cdot(\text{Lebesgue on }[0,\infty))\otimes\mu$ (`intensity`).
--
--   **Rate profiles** (form (14), p. 10). A profile $v(\sigma,\tau,y)$ is the service rate of a job of type $(\sigma,\tau)$ with remaining time $y$; only $y\le\tau$ matters. For such a profile:
--
--   1. the service received is $\hat\sigma_v(\sigma,\tau)=\int_{-\infty}^{\tau}v(\sigma,\tau,y)\,dy$, eq. (79);
--   2. the deadline extension is $\mathrm{ext}_v(\sigma,\tau)=\sup\{-y: y\le\tau,\ v(\sigma,\tau,y)>0\}\in[0,\infty]$, with $\sup\emptyset=0$; this is $(\hat\tau-\tau)_+$ of (90);
--   3. $v$ is **feasible** if it is measurable (and so is $\mathrm{ext}_v$), $0\le v(\sigma,\tau,y)\le1$ for $(\sigma,\tau)\in S$, $y\le\tau$ (constraint (1)), and $v(\sigma,\tau,\cdot)$ is integrable on $(-\infty,\tau]$ with $\hat\sigma_v(\sigma,\tau)\le\sigma$ (constraint (80));
--   4. it **meets demands** (2) if $\hat\sigma_v=\sigma$ on $S$, and **meets deadlines** (3) if $v(\sigma,\tau,y)=0$ for $y\le0$.
--
--   **Capacity and costs** (§2, §3.1). The job $(a;\sigma,\tau)$ is served at time $t$ at rate $v(\sigma,\tau,a+\tau-t)\,\mathbf 1\{a\le t\}$, and the service capacity is $P(t)=\sum_k r_k(t)$, the integral of this rate against $N$. Then
--
--   $$\mathrm{Var}(P)=\limsup_{t\to\infty}\mathrm{Var}(P(t)),\qquad \mathrm{rate}(c)=\limsup_{T\to\infty}\frac1T\,\mathbb E\Big[\sum_{k:\,a_k+\tau_k\le T}c(\sigma_k,\tau_k)\Big],$$
--
--   and the objective of (9) is $\mathrm{cost}(v)=\mathrm{Var}(P)+\mathrm{rate}\big(\delta(\sigma-\hat\sigma_v)\big)+\mathrm{rate}\big(\varepsilon\,\mathrm{ext}_v\big)\in[0,\infty]$.
--
--   **Policies** (form (4), p. 7). A policy $u(x,y)$ sets the rate from the remaining demand $x$ and remaining time $y$. A trajectory of a job $(\sigma,\tau)$ is a continuous $x\ge0$ on $[0,\infty)$ with $x(s)=\sigma-\int_0^s u(x(s'),\tau-s')\,ds'$; $u$ **produces** $v$ at $(\sigma,\tau)$ if a trajectory exists and every trajectory has rate $v(\sigma,\tau,\tau-s)$ for a.e. $s\ge0$.
--
--   **The optimal objects.** Generalized Exact Scheduling (25), corrected:
--
--   $$u^*(x,y)=\begin{cases}x/y,& y>0,\ x/y\le\min\{\delta/2,\sqrt\varepsilon\},\\ \delta/2,& y>0,\ x/y>\delta/2,\ \delta/2\le\sqrt\varepsilon,\\ \sqrt\varepsilon\,\mathbf 1\{x>0\},& \delta/2>\sqrt\varepsilon\ \text{(otherwise)},\\ 0,& \delta/2\le\sqrt\varepsilon,\ y\le0;\end{cases}$$
--
--   the profile (96): $v^*=(\sigma/\tau)\mathbf 1\{y>0\}$ if $\sigma/\tau\le\min\{\delta/2,\sqrt\varepsilon\}$, $(\delta/2)\mathbf 1\{y>0\}$ if $\sigma/\tau>\delta/2$ and $\delta/2\le\sqrt\varepsilon$, and $\sqrt\varepsilon\,\mathbf 1\{y>\tau-\sigma/\sqrt\varepsilon\}$ otherwise; and the per-job value of (26), corrected:
--
--   $$J^*(\sigma,\tau)=\frac{\sigma^2}{\tau}\mathbf 1\Big\{\frac\sigma\tau\le\min\{\tfrac\delta2,\sqrt\varepsilon\}\Big\}+\delta\Big(\sigma-\frac{\delta\tau}4\Big)\mathbf 1\Big\{\frac\sigma\tau>\frac\delta2,\ \frac\delta2\le\sqrt\varepsilon\Big\}+(2\sqrt\varepsilon\sigma-\varepsilon\tau)\mathbf 1\Big\{\frac\sigma\tau>\sqrt\varepsilon,\ \sqrt\varepsilon<\frac\delta2\Big\},$$
--
--   with optimal value $\Lambda\,\mathbb E_\mu[J^*(\sigma,\tau)]$.
--
--   These objects carry every statement of the mission, from Lemma 2 to Theorem 4.
--
--   **Formalization Note** The printed third line of (25) reads "$\sqrt\varepsilon\,\mathbf 1\{x>0\}$ otherwise", which also serves a job after its deadline when $\delta/2<\sqrt\varepsilon$ and is not optimal; the fourth line above is the correction. The printed indicators of (26), $\mathbf 1\{\sigma/\tau>\delta/2\ge\sqrt\varepsilon\}$ and $\mathbf 1\{\sigma/\tau>\sqrt\varepsilon>\delta/2\}$, are reversed and are corrected. $E[U]$, $E[W]$ are read as long-run rates, because at a fixed time no job has its deadline almost surely. Stationary quantities are $\limsup$s as $t\to\infty$ with arrivals on $[0,\infty)$; the continuity equation (5) is not formalized. $\mathrm{Var}(P)$ and the penalty rates are computed from the point process, never from a closed form. Lean's $x/0=0$ only matters at $\sigma=\tau=0$, where every quantity is $0$.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, §2 pp. 4–5 (jobs, (1)–(3), P(t), U(t), W(t)), §3.1 pp. 7–8 (intensity, (4), problem (9)), (14) p. 10, (25) and (26) p. 13, (79)–(80) p. 39, (90) p. 40, (96) p. 41

import Mathlib
import Definitions.Def_GenExactSched_PoissonRandomMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-! # The stationary deadline-scheduling model of Nakahira–Ferragut–Wierman

Nakahira–Ferragut–Wierman, *Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline
Scheduler*, arXiv:2004.12280v2, §2 (pp. 4–5), §3.1 (pp. 7–8), (14) p. 10, (25) p. 13, Appendices
C–E (pp. 39–43).

A job is a point `p = (a, (σ, τ))` of `ℝ × (ℝ × ℝ)`: arrival time `a`, demand `σ`, sojourn time
`τ`; a mark is `q = (σ, τ)` with `q.1 = σ`, `q.2 = τ`. A rate profile `v σ τ y` is the service
rate of a job of type `(σ, τ)` when its remaining time is `y` (policy class (14), p. 10). -/

/-- **Standing assumptions on the job types and their law**, arXiv:2004.12280v2, §2 p. 4:
"S is bounded, and S ⊂ {(σ, τ) : τ ≥ σ and σ ≥ 0}"; the mark law `μ` (the paper's `f(σ, τ)`) is a
probability measure carried by `S`.

**Formalization Note.** `μ` is any probability measure on `S`; no density is assumed. Finite first
and second moments of `σ, τ` follow from boundedness and are not stated separately. -/
structure MarkAssumptions (S : Set (ℝ × ℝ)) (μ : Measure (ℝ × ℝ)) : Prop where
  measurableSet : MeasurableSet S
  bounded : Bornology.IsBounded S
  subset : S ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ q.2}
  isProbability : IsProbabilityMeasure μ
  null_compl : μ Sᶜ = 0

/-- **Intensity of the stationary marked arrival process**, arXiv:2004.12280v2, §3.1 p. 7:
`Λ(a, σ, τ) = Λ f(σ, τ)`, i.e. `Λ · (Lebesgue on arrival times) ⊗ μ`.

**Formalization Note.** Arrival times range over `[0, ∞)`; the stationary quantities of the paper
are recovered as `t → ∞` limits (`statVar`, `penaltyRate`). -/
noncomputable def intensity (Λ : ℝ) (μ : Measure (ℝ × ℝ)) : Measure (ℝ × (ℝ × ℝ)) :=
  ENNReal.ofReal Λ • (volume.restrict (Set.Ici (0 : ℝ))).prod μ

/-- **Total service received** `σ̂_v(σ, τ) = ∫_{-∞}^{τ} v(σ, τ, y) dy`, arXiv:2004.12280v2,
(79), p. 39.

**Formalization Note.** A Bochner integral; `Feasible` requires its integrand to be integrable on
`(-∞, τ]` for every job type in `S`, so no junk value enters. -/
noncomputable def σhat (v : ℝ → ℝ → ℝ → ℝ) (σ τ : ℝ) : ℝ :=
  ∫ y in Set.Iic τ, v σ τ y

/-- **Deadline extension** `(τ̂ − τ)₊` of a job of type `(σ, τ)` under the profile `v`,
arXiv:2004.12280v2, (90), p. 40: the supremum of `−y` over the remaining times `y ≤ τ` at which
the job is served at a positive rate, and `0` if it is never served after its deadline.

**Formalization Note.** An `ℝ≥0∞`-valued supremum: a job served at positive rates arbitrarily
long after its deadline has extension `∞`, and the empty supremum is `0` (the first case of
(90)). The supremum is pointwise, as in (90), not an essential supremum. -/
noncomputable def ext (v : ℝ → ℝ → ℝ → ℝ) (σ τ : ℝ) : ℝ≥0∞ :=
  ⨆ (y : ℝ) (_ : y ≤ τ ∧ 0 < v σ τ y), ENNReal.ofReal (-y)

/-- **Feasible rate profiles of form (14) under the rate constraint (1)**, arXiv:2004.12280v2,
(1) p. 4, (14) p. 10, (80) p. 39. A profile `v` is feasible on the job types `S` when

1. `(σ, τ, y) ↦ v σ τ y` is measurable, and so is the extension `(σ, τ) ↦ ext v σ τ`;
2. for `(σ, τ) ∈ S` and `y ≤ τ`, `0 ≤ v σ τ y ≤ 1` (constraint (1));
3. for `(σ, τ) ∈ S`, `y ↦ v σ τ y` is integrable on `(-∞, τ]` and the service received does not
   exceed the demand, `σ̂_v(σ, τ) ≤ σ` (constraint (80)).

**Formalization Note.** Values at `y > τ` (before arrival) never enter. Measurability is required
on all of `ℝ³`; any profile measurable on the relevant domain agrees there with such a profile.
Measurability of the extension is needed for the deadline penalty to be defined. -/
structure Feasible (S : Set (ℝ × ℝ)) (v : ℝ → ℝ → ℝ → ℝ) : Prop where
  measurable : Measurable (fun p : ℝ × ℝ × ℝ => v p.1 p.2.1 p.2.2)
  measurable_ext : Measurable (fun q : ℝ × ℝ => ext v q.1 q.2)
  rate_mem : ∀ q ∈ S, ∀ y ≤ q.2, 0 ≤ v q.1 q.2 y ∧ v q.1 q.2 y ≤ 1
  integrableOn : ∀ q ∈ S, IntegrableOn (v q.1 q.2) (Set.Iic q.2)
  σhat_le : ∀ q ∈ S, σhat v q.1 q.2 ≤ q.1

/-- **Demand constraint (2)**, arXiv:2004.12280v2, p. 4, for a profile of form (14): every job
receives its full demand, `σ̂_v(σ, τ) = σ` on `S`. -/
def MeetsDemand (S : Set (ℝ × ℝ)) (v : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ q ∈ S, σhat v q.1 q.2 = q.1

/-- **Deadline constraint (3)**, arXiv:2004.12280v2, p. 4, for a profile of form (14):
`r_k(t) ≤ 1{a_k ≤ t < a_k + τ_k}`, i.e. no service at remaining times `y ≤ 0`. -/
def MeetsDeadline (S : Set (ℝ × ℝ)) (v : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ q ∈ S, ∀ y ≤ 0, v q.1 q.2 y = 0

/-- **Service rate of the job `p = (a, (σ, τ))` at time `t`** under the profile `v`,
arXiv:2004.12280v2, (14) p. 10: `r(t) = v(σ, τ, a + τ − t)` once the job has arrived (`a ≤ t`),
and `0` before. -/
noncomputable def jobRate (v : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ :=
  if p.1 ≤ t then v p.2.1 p.2.2 (p.1 + p.2.2 - t) else 0

/-- **Service capacity** `P(t) = Σ_k r_k(t)`, arXiv:2004.12280v2, §2 p. 4, for the arrival
measure `N ω`.

**Formalization Note.** The sum over jobs is the integral of `jobRate v t` against the point
measure `N ω`. It is a Bochner integral; Campbell's formula (Theorem 7, `campbell_poisson`) makes
it absolutely convergent for almost every `ω`, so its junk value on a null set affects no moment. -/
noncomputable def capacity {Ω : Type*} (N : Ω → Measure (ℝ × (ℝ × ℝ)))
    (v : ℝ → ℝ → ℝ → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ p, jobRate v t p ∂(N ω)

/-- **Stationary variance of the service capacity** `Var(P)`, arXiv:2004.12280v2, §3.1 pp. 7–8:
the variance of `P(t)` as `t → ∞`.

**Formalization Note.** Defined as the `limsup` of the `ℝ≥0∞`-valued variance `evariance`, so the
existence of the limit is not assumed (Lemma 2, `lemma_2`, proves it is a limit). It is computed
from the point process, not from a closed form. -/
noncomputable def statVar {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (v : ℝ → ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun t : ℝ => evariance (capacity N v t) P) Filter.atTop

/-- **Long-run penalty rate** for a per-job penalty `c(σ, τ)`, arXiv:2004.12280v2, §2 p. 5 (the
penalties `U(t)`, `W(t)` of jobs with deadline `t`) and (81), p. 39: the expected total penalty of
jobs whose deadline `a + τ` falls in `[0, T]`, divided by `T`, as `T → ∞`.

**Formalization Note.** The paper's `E[U]`, `E[W]` sum over jobs with deadline exactly `t`; at a
fixed `t` that sum is almost surely empty, so they are read as long-run rates (the value (81)
shows this is meant). `limsup` is used so the existence of the limit is not assumed (`eq_81`
proves it is a limit). -/
noncomputable def penaltyRate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (c : ℝ × ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℝ => (ENNReal.ofReal T)⁻¹ *
    ∫⁻ ω, ∫⁻ p, Set.indicator {p : ℝ × (ℝ × ℝ) | p.1 + p.2.2 ≤ T} (fun p => c p.2) p ∂(N ω) ∂P)
    Filter.atTop

/-- **Per-job penalty for unmet demand** `δ(σ − σ̂_v(σ, τ))`, arXiv:2004.12280v2, §2 p. 5 and (81),
p. 39. -/
noncomputable def demandPenalty (δ : ℝ) (v : ℝ → ℝ → ℝ → ℝ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (δ * (q.1 - σhat v q.1 q.2))

/-- **Per-job penalty for deadline extension** `ε(τ̂ − τ)₊`, arXiv:2004.12280v2, §2 p. 5 and
p. 40. -/
noncomputable def extPenalty (ε : ℝ) (v : ℝ → ℝ → ℝ → ℝ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ε * ext v q.1 q.2

/-- **Objective of problem (9)/(95)**, arXiv:2004.12280v2, (9) p. 8 and (95) p. 41:
`Var(P) + E[δU] + E[εW]`, each penalty counted once.

**Formalization Note.** Values in `ℝ≥0∞`; an infinite extension gives cost `∞`. -/
noncomputable def cost {Ω : Type*} [MeasurableSpace Ω] (δ ε : ℝ) (P : Measure Ω)
    (N : Ω → Measure (ℝ × (ℝ × ℝ))) (v : ℝ → ℝ → ℝ → ℝ) : ℝ≥0∞ :=
  statVar P N v + penaltyRate P N (demandPenalty δ v) + penaltyRate P N (extPenalty ε v)

/-- **Trajectory of a job under a distributed policy of form (4)**, arXiv:2004.12280v2, (4) p. 7:
the remaining demand `x(s)` of a job of type `(σ, τ)` at elapsed time `s ≥ 0` (remaining time
`τ − s`), served at rate `u(x(s), τ − s)`. It is continuous and nonnegative on `[0, ∞)`, starts at
`x(0) = σ`, and satisfies `x(s) = σ − ∫₀ˢ u(x(s'), τ − s') ds'` with an integrable rate. -/
def IsTrajectory (u : ℝ → ℝ → ℝ) (σ τ : ℝ) (x : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ (∀ s, 0 ≤ s → 0 ≤ x s) ∧ x 0 = σ ∧
    ∀ s, 0 ≤ s → IntegrableOn (fun s' => u (x s') (τ - s')) (Set.Icc 0 s) ∧
      x s = σ - ∫ s' in (0 : ℝ)..s, u (x s') (τ - s')

/-- **A policy of form (4) produces a rate profile at a job type**, arXiv:2004.12280v2, App. E
p. 43 ("scheduler (25) of the form (4) can produce identical service rates to (96)"): the policy
`u` has a trajectory for the job `(σ, τ)`, and along every trajectory the realized rate at elapsed
time `s` equals `v(σ, τ, τ − s)` for almost every `s ≥ 0`. -/
def Produces (u : ℝ → ℝ → ℝ) (v : ℝ → ℝ → ℝ → ℝ) (σ τ : ℝ) : Prop :=
  (∃ x, IsTrajectory u σ τ x) ∧
    ∀ x, IsTrajectory u σ τ x →
      ∀ᵐ s ∂(volume.restrict (Set.Ici (0 : ℝ))), u (x s) (τ - s) = v σ τ (τ - s)

/-- **Generalized Exact Scheduling, policy (25), corrected**, arXiv:2004.12280v2, p. 13. With
`x` the remaining demand and `y` the remaining time:

* `x / y` if `y > 0` and `x / y ≤ min{δ/2, √ε}`;
* `δ/2` if `y > 0`, `x / y > δ/2` and `δ/2 ≤ √ε`;
* `√ε · 1{x > 0}` if `δ/2 > √ε` (and not the first case);
* `0` if `δ/2 ≤ √ε` and `y ≤ 0`.

**Formalization Note.** The printed third line is "`√ε 1{x > 0}` otherwise", which also applies
when `δ/2 ≤ √ε` and `y ≤ 0`; it keeps serving a job past its deadline at rate `√ε` and is not
optimal (`σ = τ = 1`, `δ = ε = 1`: cost `5/4` instead of `3/4`). The fourth line is the
correction: in the regime `δ/2 ≤ √ε` every job leaves at its deadline. -/
noncomputable def uStar (δ ε : ℝ) (x y : ℝ) : ℝ :=
  if 0 < y ∧ x / y ≤ min (δ / 2) (Real.sqrt ε) then x / y
  else if 0 < y ∧ δ / 2 < x / y ∧ δ / 2 ≤ Real.sqrt ε then δ / 2
  else if Real.sqrt ε < δ / 2 then Real.sqrt ε * (if 0 < x then 1 else 0)
  else 0

/-- **The optimal rate profile (96)**, arXiv:2004.12280v2, Lemma 9, p. 41:

* `(σ/τ) 1{y > 0}` if `σ/τ ≤ min{δ/2, √ε}`;
* `(δ/2) 1{y > 0}` if `σ/τ > δ/2` and `δ/2 ≤ √ε`;
* `√ε 1{y > τ − σ/√ε}` otherwise.

**Formalization Note.** Lean's `σ / 0 = 0`; on `S` the sojourn time `τ = 0` forces `σ = 0`, where
the first case gives rate `0`. -/
noncomputable def vStar (δ ε : ℝ) (σ τ y : ℝ) : ℝ :=
  if σ / τ ≤ min (δ / 2) (Real.sqrt ε) then (if 0 < y then σ / τ else 0)
  else if δ / 2 < σ / τ ∧ δ / 2 ≤ Real.sqrt ε then (if 0 < y then δ / 2 else 0)
  else (if τ - σ / Real.sqrt ε < y then Real.sqrt ε else 0)

/-- **Optimal per-job cost, the integrand of (26), corrected**, arXiv:2004.12280v2, p. 13:

`J*(σ, τ) = (σ²/τ) 1{σ/τ ≤ min{δ/2, √ε}} + δ(σ − δτ/4) 1{σ/τ > δ/2, δ/2 ≤ √ε}
  + (2√ε σ − ετ) 1{σ/τ > √ε, √ε < δ/2}`.

**Formalization Note.** The printed indicators are `1{σ/τ > δ/2 ≥ √ε}` and `1{σ/τ > √ε > δ/2}`;
they are reversed relative to (25), (96) and §3.5 (`σ = 3/4`, `τ = 1`, `δ = 2`, `ε = 1/4`: no printed
indicator fires, while the per-job optimum is `1/2`). The three corrected indicators are disjoint and
cover every case. -/
noncomputable def Jstar (δ ε : ℝ) (σ τ : ℝ) : ℝ :=
  (if σ / τ ≤ min (δ / 2) (Real.sqrt ε) then σ ^ 2 / τ else 0)
  + (if δ / 2 < σ / τ ∧ δ / 2 ≤ Real.sqrt ε then δ * (σ - δ * τ / 4) else 0)
  + (if Real.sqrt ε < σ / τ ∧ Real.sqrt ε < δ / 2 then 2 * Real.sqrt ε * σ - ε * τ else 0)

/-- **The optimal value (26), corrected**, arXiv:2004.12280v2, p. 13: `Λ · E_μ[J*(σ, τ)]`. -/
noncomputable def optVal (Λ δ ε : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ :=
  Λ * ∫ q, Jstar δ ε q.1 q.2 ∂μ

end GenExactSched


