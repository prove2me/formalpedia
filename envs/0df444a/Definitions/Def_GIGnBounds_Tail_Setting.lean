-- Prove2me | Definitions.Def_GIGnBounds_Tail_Setting
-- name    : GIGnBounds_Tail_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:04.796733+00:00
-- url     : https://prove2.me/theorems/d97d797c-d75c-45a7-b308-99bb4222f474
-- title:
--   pp. 7–9, 36 — laws of A and S, μ_A, μ_S, ρ, normalised moments, r*, equilibrium law, renewal processes, the FCFS GI/GI/n queue and its steady state
-- statement:
--   This file fixes the objects of §2.1 of Li and Goldberg (pp. 7–9), on which every statement of the mission is built.
--
--   1. **Time laws.** The inter-arrival time $A$ and the service time $S$ are given by their laws $\mu_A$ and $\mu_S$, probability measures on $\mathbb R$ concentrated on $[0,\infty)$ with $0<\mathbb E[X]<\infty$. Write $\mathbb E[X]=\int x\,d\mu(x)$, the **rate** $\mu_X = 1/\mathbb E[X]$ (p. 2), the **traffic intensity** $\rho=\mu_A/(n\mu_S)$ (p. 8), and the **normalised moment** $\mathbb E[(X\mu_X)^r]=\int (x\mu_X)^r\,d\mu(x)$.
--
--   2. **Moment index.** $r^*=\sup\{r:\mathbb E[S^r]<\infty\}$ (p. 9), an extended real number which may equal $+\infty$.
--
--   3. **Equilibrium law.** $R(X)$ is the law on $(0,\infty)$ with density $z\mapsto \mu_X\,\mathbb P(X>z)$, so that $\mathbb P(R>y)=\frac{1}{\mathbb E[X]}\int_y^\infty \mathbb P(X>z)\,dz$ for $y>0$ (p. 7).
--
--   4. **Renewal counting.** With intervals $X_1,X_2,\dots$ an *ordinary* renewal process has renewals at $X_1, X_1+X_2,\dots$; an *equilibrium* one has its first renewal at an independent $R$ distributed as $R(X)$, and later ones at $R+X_1, R+X_1+X_2,\dots$. The counting function at $t$ is the number of renewals in $[0,t]$ (p. 7).
--
--   5. **Bounding family** (p. 7). A *service family* of size $m$ is a mutually independent collection $\{\mathcal N_{e,i}, 1\le i\le m\}$ of equilibrium renewal processes with renewals distributed as $S$; a *renewal family* adds an independent equilibrium renewal process $\mathcal A_e$ with renewals distributed as $A$. $A_e(t)$, $N_{e,i}(t)$ are the counts in $[0,t]$, and $A_o(t)$ is the ordinary renewal process formed by the renewals of $\mathcal A_e$ after the first one, restarted at $0$, so that $A_e(t)\le 1+A_o(t)$ (coupling (7), p. 24). An *i.i.d. sequence* of law $\mu$ is also defined.
--
--   6. **Suprema.** $\sup_{t\ge0} f(t)$ and $\sup_{0\le s\le t} f(s)$ are taken in the extended reals.
--
--   7. **The FCFS GI/GI/n queue** (p. 7). An initial condition is $z=(T_0,w)$: the first arrival occurs at time $T_0\ge0$, and server $i$ holds a job with residual service time $w_i\ge0$ ($w_i=0$ means idle); no job waits at time $0$. Arrival $k=0,1,\dots$ occurs at $T_0+a_0+\dots+a_{k-1}$ and brings service time $s_k$. The sorted workload vector found by arrival $k$ follows the Kiefer–Wolfowitz recursion: arrival $k$ joins the least-loaded server (FCFS), its delay is the smallest workload it finds, and it leaves at arrival time + delay + $s_k$. $Q(t)$, the number in system at time $t$, counts initial jobs still in service and arrivals present on $[\text{arrival},\text{departure})$. Under the queue law the initial condition has law $\nu_0$ and is independent of the i.i.d. pairs $(a_k,s_k)$, whose coordinates are independent with laws $\mu_A$, $\mu_S$.
--
--   8. **Steady state** (p. 8). "$Q(\infty)$ exists" with law $\pi$ on $\mathbb N$ means: for every admissible initial law $\nu_0$ (a probability law of $(T_0,w)$ with nonnegative coordinates) and every $q\in\mathbb N$, $\mathbb P_{\nu_0}(Q(t)=q)\to\pi(\{q\})$ as $t\to\infty$. Then $L(\infty)=\max(0,Q(\infty)-n)$.
--
--   9. **Residual start** (p. 36). The initial law of $\mathcal Q^{m}_{\mathrm{res}}$: first arrival distributed as $R(A)$, all $m$ servers busy with i.i.d. residual service times distributed as $R(S)$, all independent.
--
--   **Formalization Note.** Laws replace random variables. $0<\mathbb E[X]$ and integrability are explicit because Lean's $1/0=0$ is not the paper's $1/0=\infty$. $r^*$ is a supremum over $r\ge0$, which changes nothing since $r=1$ is in the set. Counts are `Nat.card` of subtypes; they are finite almost surely, so the value $0$ that Lean assigns to an infinite count only affects a null set. Sequences are indexed from $0$ (the paper's $A_i$ is the $(i-1)$-st entry); the intervals of an equilibrium renewal process are indexed by `Option ℕ`, `none` being the first. Probability-measure-ness of $\mu_A,\mu_S$ is an instance argument. The class of initial conditions excludes jobs waiting at time $0$; this narrows the hypothesis "$Q(\infty)$ exists" and so strengthens every theorem that assumes it.
-- source:
--   Li and Goldberg, Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling, arXiv:1706.04628v3, pp. 7–9 (§2.1), p. 2 (μ_X), p. 24 (coupling (7)), pp. 36–37 (𝒬_res)

import Mathlib

namespace GIGnBounds.Tail

open MeasureTheory ProbabilityTheory Filter Topology

/-! # Setting of Li–Goldberg, *Simple and explicit bounds for multi-server queues with 1/(1−ρ) scaling*

Source: arXiv:1706.04628v3, §2.1 (pp. 7–9), p. 2, p. 24 (7), pp. 36–37.

Index conventions used throughout:
* the paper's inter-arrival times `A₁, A₂, …` and service times `S₁, S₂, …` are numbered from 1; here
  every sequence is indexed by `ℕ` from 0, so the paper's `Aᵢ` is `X (i - 1)`;
* the renewal intervals of an equilibrium renewal process are indexed by `Option ℕ`: `none` is the
  first interval (distributed as the equilibrium law), `some j` is the `(j+1)`-st later interval;
* servers are `Fin n`; arrivals to the queue are numbered from 0.
-/

/-- A law on `ℝ` of a nonnegative time with finite positive mean: the laws of the paper's
inter-arrival time `A` and service time `S`. `μ_X = 1/E[X]` must be a finite positive number, so
`0 < E[X] < ∞` is required (the paper's convention `1/0 = ∞` is not Lean's). Probability-measure-ness
is carried separately as an instance argument. -/
structure IsTimeLaw (μ : Measure ℝ) : Prop where
  nonneg : μ (Set.Iio 0) = 0
  integrable : Integrable (fun x : ℝ => x) μ
  mean_pos : 0 < ∫ x, x ∂μ

/-- `E[X] = ∫ x dμ(x)`. -/
noncomputable def mean (μ : Measure ℝ) : ℝ := ∫ x, x ∂μ

/-- The rate `μ_X = 1/E[X]` (p. 2). -/
noncomputable def rate (μ : Measure ℝ) : ℝ := (mean μ)⁻¹

/-- The traffic intensity `ρ = ρ_n = μ_A/(n μ_S)` (p. 8). -/
noncomputable def rho (n : ℕ) (μA μS : Measure ℝ) : ℝ := rate μA / (n * rate μS)

/-- The normalised moment `E[(X μ_X)^r] = ∫ (x μ_X)^r dμ(x)` (real power `rpow`). It is a Bochner
integral: every use in a statement sits under a hypothesis making it finite. -/
noncomputable def nMoment (μ : Measure ℝ) (r : ℝ) : ℝ := ∫ x, (x * rate μ) ^ r ∂μ

/-- `r* = sup{r : E[S^r] < ∞}` (p. 9), an extended real (it may be `+∞`). The defining set is
restricted to `r ≥ 0`, which does not change the supremum since `r = 1` belongs to it for a time law. -/
noncomputable def rStar (μ : Measure ℝ) : EReal :=
  sSup ((fun r : ℝ => (r : EReal)) '' {r : ℝ | 0 ≤ r ∧ ∫⁻ x, ENNReal.ofReal (x ^ r) ∂μ < ⊤})

/-- The equilibrium distribution `R(X)` of a time law `μ` (p. 7): the law on `(0, ∞)` with density
`z ↦ μ_X P(X > z)`, i.e. `P(R > y) = (1/E[X]) ∫_y^∞ P(X > z) dz`. -/
noncomputable def eqLaw (μ : Measure ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun z => ENNReal.ofReal (rate μ * (μ (Set.Ioi z)).toReal))

/-- Ordinary renewal counting function (p. 7): with intervals `X 0, X 1, …` the renewals occur at
`X 0, X 0 + X 1, …`, and `ordCount X t` is the number of renewals in `[0, t]`. (`Nat.card` of an
infinite set is `0`; for a.s. finite counts this only affects a null set.) -/
noncomputable def ordCount (X : ℕ → ℝ) (t : ℝ) : ℕ :=
  Nat.card {k : ℕ // ∑ j ∈ Finset.range (k + 1), X j ≤ t}

/-- Equilibrium (delayed) renewal counting function (p. 7): the first renewal is at `R`, the later
ones at `R + X 0, R + X 0 + X 1, …`; `eqCount R X t` is the number of renewals in `[0, t]`. -/
noncomputable def eqCount (R : ℝ) (X : ℕ → ℝ) (t : ℝ) : ℕ :=
  Nat.card {k : ℕ // R + ∑ j ∈ Finset.range k, X j ≤ t}

/-- An i.i.d. sequence of real random variables with common law `μ`. -/
structure IsIIDSeq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (μ : Measure ℝ) : Prop where
  measurable : ∀ j, Measurable (X j)
  indep : iIndepFun X P
  law : ∀ j, P.map (X j) = μ

/-- A mutually independent collection `{𝒩_{e,i}, 1 ≤ i ≤ m}` of equilibrium renewal processes with
renewals distributed as `S` (p. 7), given by their renewal intervals: `srv i none` is the first
(equilibrium, law `R(S)`) interval of server `i`, `srv i (some j)` its later intervals (law `S`). -/
structure ServiceFamily (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (m : ℕ)
    (μS : Measure ℝ) where
  srv : Fin m → Option ℕ → Ω → ℝ
  measurable_srv : ∀ i j, Measurable (srv i j)
  law_srv_none : ∀ i, P.map (srv i none) = eqLaw μS
  law_srv_some : ∀ i j, P.map (srv i (some j)) = μS
  indep_srv : iIndepFun (fun (p : Fin m × Option ℕ) (ω : Ω) => srv p.1 p.2 ω) P

/-- `N_{e,i}(t)`: the number of renewals in `[0, t]` of the `i`-th equilibrium renewal process. -/
noncomputable def ServiceFamily.Ne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}
    {μS : Measure ℝ} (F : ServiceFamily Ω P m μS) (i : Fin m) (ω : Ω) (t : ℝ) : ℕ :=
  eqCount (F.srv i none ω) (fun j => F.srv i (some j) ω) t

/-- The paper's bounding family (p. 7): `{𝒩_{e,i}, 1 ≤ i ≤ m}` as in `ServiceFamily`, together with an
independent equilibrium renewal process `𝒜_e` with renewals distributed as `A`, given by its intervals
`arr none` (law `R(A)`) and `arr (some j)` (law `A`). All intervals of all processes are mutually
independent. -/
structure RenewalFamily (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (m : ℕ)
    (μA μS : Measure ℝ) extends ServiceFamily Ω P m μS where
  arr : Option ℕ → Ω → ℝ
  measurable_arr : ∀ j, Measurable (arr j)
  law_arr_none : P.map (arr none) = eqLaw μA
  law_arr_some : ∀ j, P.map (arr (some j)) = μA
  indep_all : iIndepFun (fun (k : Option ℕ ⊕ (Fin m × Option ℕ)) (ω : Ω) =>
    Sum.elim (fun j => arr j ω) (fun p => srv p.1 p.2 ω) k) P

/-- `A_e(t)`: the number of renewals in `[0, t]` of the equilibrium arrival renewal process `𝒜_e`. -/
noncomputable def RenewalFamily.Ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}
    {μA μS : Measure ℝ} (F : RenewalFamily Ω P m μA μS) (ω : Ω) (t : ℝ) : ℕ :=
  eqCount (F.arr none ω) (fun j => F.arr (some j) ω) t

/-- `A_o(t)`: the ordinary renewal process formed by the event times of `𝒜_e` after the first one,
re-started at time 0 (the coupling (7), p. 24, under which `A_e(t) ≤ 1 + A_o(t)`). -/
noncomputable def RenewalFamily.Ao {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}
    {μA μS : Measure ℝ} (F : RenewalFamily Ω P m μA μS) (ω : Ω) (t : ℝ) : ℕ :=
  ordCount (fun j => F.arr (some j) ω) t

/-- `N_{e,i}(t)` for the service processes of a `RenewalFamily`. -/
noncomputable def RenewalFamily.Ne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m : ℕ}
    {μA μS : Measure ℝ} (F : RenewalFamily Ω P m μA μS) (i : Fin m) (ω : Ω) (t : ℝ) : ℕ :=
  F.toServiceFamily.Ne i ω t

/-- `sup_{t ≥ 0} f(t)` as an extended real (never a junk value). -/
noncomputable def supFrom (f : ℝ → ℝ) : EReal :=
  ⨆ t : ℝ, ⨆ (_ : 0 ≤ t), (f t : EReal)

/-- `sup_{0 ≤ s ≤ t} f(s)` as an extended real. -/
noncomputable def supUpTo (f : ℝ → ℝ) (t : ℝ) : EReal :=
  ⨆ s : ℝ, ⨆ (_ : 0 ≤ s ∧ s ≤ t), (f s : EReal)

/-! ## The FCFS GI/GI/n queue (Kiefer–Wolfowitz workload recursion) -/

/-- The increasing rearrangement of a vector. -/
noncomputable def sortVec {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ := v ∘ ⇑(Tuple.sort v)

/-- Arrival time of arrival `k` (numbered from 0): `T₀ + a 0 + ⋯ + a (k-1)`, where the initial
condition `z = (T₀, w)` has first-arrival time `z.1 = T₀`. -/
def arrTime {n : ℕ} (z : ℝ × (Fin n → ℝ)) (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  z.1 + ∑ j ∈ Finset.range k, a j

/-- The sorted vector of remaining workloads at the `n` servers found by arrival `k`
(Kiefer–Wolfowitz). Initial condition `z = (T₀, w)`: `w i ≥ 0` is the residual service time at time 0
of the job in service at server `i` (`0` = idle); `a k` is the time between arrivals `k` and `k+1`,
`s k` the service time of arrival `k`. Arrival `k` joins the least-loaded server (FCFS). -/
noncomputable def work {n : ℕ} (z : ℝ × (Fin n → ℝ)) (a s : ℕ → ℝ) : ℕ → Fin n → ℝ
  | 0 => sortVec (fun i => max (z.2 i - z.1) 0)
  | k + 1 => sortVec (fun i => max (work z a s k i + (if (i : ℕ) = 0 then s k else 0) - a k) 0)

/-- The delay (waiting time in queue) of arrival `k` under FCFS: the smallest remaining workload it
finds. (For `n = 0` the value `0` is a placeholder; every statement assumes `0 < n`.) -/
noncomputable def delay {n : ℕ} (z : ℝ × (Fin n → ℝ)) (a s : ℕ → ℝ) (k : ℕ) : ℝ :=
  if h : 0 < n then work z a s k ⟨0, h⟩ else 0

/-- The number of jobs in system (in service + waiting) at time `t`: initial jobs still in service,
plus arrivals present on `[arrival, departure)` (right-continuous paths). -/
noncomputable def numInSystem {n : ℕ} (z : ℝ × (Fin n → ℝ)) (a s : ℕ → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => t < z.2 i)).card +
    Nat.card {k : ℕ // arrTime z a k ≤ t ∧ t < arrTime z a k + delay z a s k + s k}

/-- Sample space of the queue: an initial condition and the sequence of (inter-arrival time, service
time) pairs. -/
abbrev QueueSpace (n : ℕ) : Type := (ℝ × (Fin n → ℝ)) × (ℕ → ℝ × ℝ)

/-- `Q(t)` evaluated on a sample point of `QueueSpace n`. -/
noncomputable def queueLength {n : ℕ} (ω : QueueSpace n) (t : ℝ) : ℕ :=
  numInSystem ω.1 (fun j => (ω.2 j).1) (fun j => (ω.2 j).2) t

/-- The law of the FCFS GI/GI/n queue with initial law `ν₀`: the initial condition is independent of
the i.i.d. pairs (inter-arrival time, service time), whose two coordinates are independent with laws
`μA` and `μS`. -/
noncomputable def queueMeasure (n : ℕ) (μA μS : Measure ℝ) [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS] (ν₀ : Measure (ℝ × (Fin n → ℝ))) : Measure (QueueSpace n) :=
  ν₀.prod (Measure.infinitePi (fun _ : ℕ => μA.prod μS))

/-- An admissible initial law: a probability law of `(T₀, w)` with nonnegative first-arrival time and
nonnegative residual service times (no jobs waiting at time 0). -/
def IsInitLaw (n : ℕ) (ν₀ : Measure (ℝ × (Fin n → ℝ))) : Prop :=
  IsProbabilityMeasure ν₀ ∧ ∀ᵐ z ∂ν₀, 0 ≤ z.1 ∧ ∀ i, 0 ≤ z.2 i

/-- "Q(∞) exists" (p. 8), with `π` the law of `Q(∞)`: from every admissible initial law, the number in
system `Q(t)` converges in distribution, as `t → ∞`, to `π`. -/
def IsSteadyStateLaw (n : ℕ) (μA μS : Measure ℝ) [IsProbabilityMeasure μA]
    [IsProbabilityMeasure μS] (π : Measure ℕ) : Prop :=
  IsProbabilityMeasure π ∧
    ∀ ν₀ : Measure (ℝ × (Fin n → ℝ)), IsInitLaw n ν₀ → ∀ q : ℕ,
      Tendsto (fun t : ℝ => queueMeasure n μA μS ν₀ {ω | queueLength ω t = q}) atTop (𝓝 (π {q}))

/-- The initial law of `𝒬^{n}_res` (p. 36): first arrival distributed as `R(A)`, and all `n` servers
busy with i.i.d. residual service times distributed as `R(S)`, all independent. -/
noncomputable def resInit (n : ℕ) (μA μS : Measure ℝ) : Measure (ℝ × (Fin n → ℝ)) :=
  (eqLaw μA).prod (Measure.pi (fun _ : Fin n => eqLaw μS))

end GIGnBounds.Tail


