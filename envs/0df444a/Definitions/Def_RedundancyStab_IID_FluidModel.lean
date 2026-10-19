-- Prove2me | Definitions.Def_RedundancyStab_IID_FluidModel
-- name    : RedundancyStab_IID_FluidModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:38.807116+00:00
-- url     : https://prove2.me/theorems/00e3a5c8-5b9f-40a6-9071-3b87e6df3978
-- title:
--   (2)–(3), p. 6 — the fluid-scaled PS and ROS systems built from common Poisson primitives, and their fluid limits (u.o.c.)
-- statement:
--   The fluid scaling of §4.1 compares the systems started from larger and larger initial states, all driven by the same randomness.
--
--   1. **Primitives.** On one probability space: for every type $c$, i.i.d. $\mathrm{Exp}(\lambda/\binom{K}{d})$ interarrival times, whose epochs form the Poisson process $\tilde A_c$; i.i.d. $\mathrm{Exp}(\mu)$ inter-epoch times, whose epochs form the Poisson process $\tilde S_c$; and an i.i.d. $\mathrm{Uniform}[0,1]$ sequence used for the random choices of ROS. All of them are mutually independent.
--   2. **Sample paths.** For an initial state $\vec N(0)\in\mathbb N^C$ the system is built event by event. $T_c(t)=\sum_{s\in c}T_{s,c}(t)$ is the cumulative capacity spent on type-$c$ jobs; between events it grows at rate $\sum_{s\in c}N_c/M_s$ under PS and at rate (number of servers serving a type-$c$ copy) under ROS. A type-$c$ arrival happens at the next epoch of $\tilde A_c$, and a type-$c$ departure happens when $T_c$ reaches the next epoch of $\tilde S_c$, so that
--   $$N_c(t)=N_c(0)+\tilde A_c(t)-\tilde S_c\big(T_c(t)\big).$$
--   Under ROS a departing type-$c$ job is in class $(c,A)$ with probability proportional to $|A|k_{c,A}$, and the freed servers pick uniformly from their queues, both decided by fresh uniforms. The ROS initial configuration places the initial jobs one by one as arrivals.
--   3. **Fluid scaling.** For $r>0$ and $\vec n(0)\in\mathbb R_{\ge0}^C$, $N^{r}$ is the system with $N^{r}_c(0)=\lfloor r\,n_c(0)\rfloor$, and the fluid-scaled processes are $N^{r}_c(rt)/r$ and $T^{r}_c(rt)/r$ (display (2)).
--   4. **Fluid limit.** $(\vec n,\vec\tau)$ is a fluid limit at the sample point $\omega$ if for some $r_j\to\infty$, $r_j>0$, and every type $c$,
--   $$\frac{N^{r_j}_c(r_jt)}{r_j}\to n_c(t),\qquad \frac{T^{r_j}_c(r_jt)}{r_j}\to\tau_c(t)\qquad\text{u.o.c.},$$
--   i.e. uniformly on $[0,T]$ for every $T\ge0$ (display (3)).
--
--   These are the objects of Lemma 1, Lemma 2 and the emptying-time step of the proof of Proposition 3.
--
--   **Formalization Note** Laws are stated as `Measure.map X ℙ = expMeasure ν` and `= volume.restrict (Icc 0 1)`, independence as `iIndepFun` of the whole family. The paths are defined by event recursion (`psPath`, `rosPath`), one event per step (simultaneous events, a null event, are processed at successive steps with zero elapsed time); `N` is piecewise constant and `T` piecewise linear between event times; beyond an accumulation of event times (a null event) the junk value is the initial interval. The printed initial condition $N^{r}_c(0)=r\,n_c(0)$ is integral only for special $r$; the formalization uses $\lfloor r\,n_c(0)\rfloor$. Fluid-limit functions are $\mathbb R\to\mathbb R$ and constrained only on $t\ge0$. `Policy` selects PS or ROS.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, p. 6, §4.1, display (2), Lemma 1 display (3) and footnote 1

import Mathlib
import Definitions.Def_RedundancyStab_IID_ROSChain

namespace RedundancyStab.IID

open Finset MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- All primitives as one family of real random variables, indexed by
`(c, i)` (interarrival times), `(c, i)` (service inter-epoch times) and `i` (uniforms). -/
def primitiveFamily {K d : ℕ} {Ω : Type*} (arr svc : JobType K d → ℕ → Ω → ℝ) (u : ℕ → Ω → ℝ) :
    (JobType K d × ℕ) ⊕ ((JobType K d × ℕ) ⊕ ℕ) → Ω → ℝ
  | Sum.inl p => arr p.1 p.2
  | Sum.inr (Sum.inl p) => svc p.1 p.2
  | Sum.inr (Sum.inr i) => u i

/-- The stochastic primitives of the fluid-scaled systems (2), p. 6, on one probability space:
for every type `c`, the i.i.d. `Exp(λ / C(K,d))` interarrival times `arrClock c i` of the Poisson
process `Ã_c` and the i.i.d. `Exp(μ)` inter-epoch times `svcClock c i` of the Poisson process
`S̃_c`; and an i.i.d. `Uniform[0,1]` sequence `unif i` deciding the random choices of ROS. All
of these random variables are mutually independent. Every system `N^{r}`, for every `r` and
every initial state, is built from these same primitives, as (2) says. -/
structure Primitives (K d : ℕ) (lam μ : ℝ) (Ω : Type*) [MeasureSpace Ω] where
  arrClock : JobType K d → ℕ → Ω → ℝ
  svcClock : JobType K d → ℕ → Ω → ℝ
  unif : ℕ → Ω → ℝ
  measurable_arr : ∀ c i, Measurable (arrClock c i)
  measurable_svc : ∀ c i, Measurable (svcClock c i)
  measurable_unif : ∀ i, Measurable (unif i)
  arr_law : ∀ c i, Measure.map (arrClock c i) ℙ = expMeasure (lam / (K.choose d : ℝ))
  svc_law : ∀ c i, Measure.map (svcClock c i) ℙ = expMeasure μ
  unif_law : ∀ i, Measure.map (unif i) ℙ = (volume : Measure ℝ).restrict (Set.Icc 0 1)
  indep : iIndepFun (primitiveFamily arrClock svcClock unif) ℙ

/-- The `i`-th epoch (`i = 0, 1, …`) of the renewal sequence with inter-epoch times `clock`:
`clock 0 + ⋯ + clock i`. -/
def epoch (clock : ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ range (i + 1), clock j

/-- The counting process of the epochs, `#{i : epoch i ≤ t}`; for i.i.d. `Exp(ν)` inter-epoch
times this is a Poisson process of rate `ν` (`Ã_c`, `S̃_c` in (2), p. 6). -/
noncomputable def countingProcess (clock : ℕ → ℝ) (t : ℝ) : ℕ :=
  {i : ℕ | epoch clock i ≤ t}.ncard

/-- Choice of an element of a list with probability proportional to the weights `w`, driven by
`x ∈ [0, Σ w)`: the first element at which the cumulative weight exceeds `x`. -/
noncomputable def pickAux {α : Type*} (w : α → ℕ) : List α → ℝ → Option α
  | [], _ => none
  | a :: l, x => if x < (w a : ℝ) then some a else pickAux w l (x - w a)

/-- Choice of an element of a list with probability proportional to `w`, driven by one
`Uniform[0,1]` variable `u`. -/
noncomputable def pickByUniform {α : Type*} (w : α → ℕ) (l : List α) (u : ℝ) : Option α :=
  pickAux w l (u * ((l.map w).sum : ℝ))

/-! ### Sample paths of the PS system by event recursion -/

/-- The state of a sample path after an event: current time, the job counts `N`, the cumulative
capacities `T_c` spent on type `c` (summed over the servers of `c`), and the numbers of arrival
epochs of `Ã_c` and service epochs of `S̃_c` used so far. -/
structure PSPathState (K d : ℕ) where
  time : ℝ
  N : JobType K d → ℕ
  T : JobType K d → ℝ
  nArr : JobType K d → ℕ
  nSvc : JobType K d → ℕ

/-- The rate `dT_c/dt = Σ_{s ∈ c} N_c / M_s` at which the PS servers of `c` spend capacity on
type-`c` jobs (§4.1, p. 6). -/
noncomputable def psGrowth (K d : ℕ) (N : JobType K d → ℕ) (c : JobType K d) : ℝ :=
  ∑ s ∈ c.1, (N c : ℝ) / (copies K d N s : ℝ)

/-- The epoch of the next PS event of each kind: arrival `Sum.inl c` at the next epoch of `Ã_c`;
departure `Sum.inr c` when `T_c` reaches the next epoch of `S̃_c` (never if `T_c` is frozen). -/
noncomputable def psCandidate {K d : ℕ} (arr svc : JobType K d → ℕ → ℝ) (σ : PSPathState K d) :
    PSEvent K d → WithTop ℝ
  | Sum.inl c => (epoch (arr c) (σ.nArr c) : ℝ)
  | Sum.inr c =>
    if 0 < psGrowth K d σ.N c then
      ((σ.time + (epoch (svc c) (σ.nSvc c) - σ.T c) / psGrowth K d σ.N c : ℝ) : WithTop ℝ)
    else ⊤

open Classical in
/-- One step of the event recursion of the PS system: the earliest pending event happens (one
event per step; simultaneous events, a null event, are handled at successive steps with zero
elapsed time), the capacities `T_c` advance linearly in between. With no pending event at all
(only when there are no types) the time advances by `1` and nothing else changes. -/
noncomputable def psPathStep {K d : ℕ} (arr svc : JobType K d → ℕ → ℝ) (σ : PSPathState K d) :
    PSPathState K d :=
  let t' := univ.inf (psCandidate arr svc σ)
  if h : ∃ e, psCandidate arr svc σ e = t' ∧ t' ≠ ⊤ then
    let t := t'.untopD 0
    let T' := fun c => σ.T c + (t - σ.time) * psGrowth K d σ.N c
    match h.choose with
    | Sum.inl c =>
      { time := t, N := Function.update σ.N c (σ.N c + 1), T := T',
        nArr := Function.update σ.nArr c (σ.nArr c + 1), nSvc := σ.nSvc }
    | Sum.inr c =>
      { time := t, N := Function.update σ.N c (σ.N c - 1), T := T',
        nArr := σ.nArr, nSvc := Function.update σ.nSvc c (σ.nSvc c + 1) }
  else { σ with time := σ.time + 1 }

/-- The sequence of post-event states of the PS system started from `N0` at time `0`. -/
noncomputable def psPath {K d : ℕ} (arr svc : JobType K d → ℕ → ℝ) (N0 : JobType K d → ℕ) :
    ℕ → PSPathState K d
  | 0 => { time := 0, N := N0, T := 0, nArr := 0, nSvc := 0 }
  | j + 1 => psPathStep arr svc (psPath arr svc N0 j)

/-! ### Sample paths of the ROS system by event recursion -/

/-- The state of a ROS sample path after an event: time, the class counts `k`, the cumulative
capacities `T_c`, the numbers of epochs of `Ã_c` and `S̃_c` used, and the number of uniforms
used. -/
structure RosPathState (K d : ℕ) where
  time : ℝ
  k : RosState K d
  T : JobType K d → ℝ
  nArr : JobType K d → ℕ
  nSvc : JobType K d → ℕ
  nUnif : ℕ

/-- The rate `dT_c/dt` under ROS: the number of servers serving a type-`c` copy,
`Σ_A |A| k c A`. -/
def rosGrowth (K d : ℕ) (k : RosState K d) (c : JobType K d) : ℝ :=
  ∑ A, (A.card : ℝ) * (k c A : ℝ)

/-- The epoch of the next ROS event of each kind (as for PS, with the ROS growth rate). -/
noncomputable def rosCandidate {K d : ℕ} (arr svc : JobType K d → ℕ → ℝ)
    (σ : RosPathState K d) : PSEvent K d → WithTop ℝ
  | Sum.inl c => (epoch (arr c) (σ.nArr c) : ℝ)
  | Sum.inr c =>
    if 0 < rosGrowth K d σ.k c then
      ((σ.time + (epoch (svc c) (σ.nSvc c) - σ.T c) / rosGrowth K d σ.k c : ℝ) : WithTop ℝ)
    else ⊤

/-- The idle servers of the list `l` each pick a waiting copy uniformly at random (ROS), the
`i`-th of them using the uniform `u (n + i)`; with an empty queue a server stays idle. -/
noncomputable def rosRefillPath {K d : ℕ} (u : ℕ → ℝ) :
    List (Fin K) → ℕ → RosState K d → RosState K d
  | [], _, k => k
  | s :: l, n, k =>
    let w : JobType K d × Finset (Fin K) → ℕ :=
      fun p => if s ∈ p.1.1 ∧ s ∉ p.2 then k p.1 p.2 else 0
    match pickByUniform w (univ : Finset (JobType K d × Finset (Fin K))).toList (u n) with
    | some p => rosRefillPath u l (n + 1) (rosStartAt K d k s p.1 p.2)
    | none => rosRefillPath u l (n + 1) k

/-- A type-`c` departure under ROS: the completing copy is uniform among the type-`c` copies in
service, so the class `(c, A)` of the leaving job is chosen with probability proportional to
`|A| k c A` (uniform `u n`); the job leaves and the servers of `A` refill (uniforms
`u (n + 1), …, u (n + |A|)`). Returns the new class counts and the number of uniforms used. -/
noncomputable def rosDepartPath {K d : ℕ} (u : ℕ → ℝ) (n : ℕ) (k : RosState K d)
    (c : JobType K d) : RosState K d × ℕ :=
  match pickByUniform (fun A : Finset (Fin K) => A.card * k c A)
      (univ : Finset (Finset (Fin K))).toList (u n) with
  | some A => (rosRefillPath u (A.sort (· ≤ ·)) (n + 1) (rosRemove K d k c A), n + 1 + A.card)
  | none => (k, n + 1)

open Classical in
/-- One step of the event recursion of the ROS system (as `psPathStep`). -/
noncomputable def rosPathStep {K d : ℕ} (arr svc : JobType K d → ℕ → ℝ) (u : ℕ → ℝ)
    (σ : RosPathState K d) : RosPathState K d :=
  let t' := univ.inf (rosCandidate arr svc σ)
  if h : ∃ e, rosCandidate arr svc σ e = t' ∧ t' ≠ ⊤ then
    let t := t'.untopD 0
    let T' := fun c => σ.T c + (t - σ.time) * rosGrowth K d σ.k c
    match h.choose with
    | Sum.inl c =>
      { time := t, k := rosArrive K d σ.k c, T := T',
        nArr := Function.update σ.nArr c (σ.nArr c + 1), nSvc := σ.nSvc, nUnif := σ.nUnif }
    | Sum.inr c =>
      { time := t, k := (rosDepartPath u σ.nUnif σ.k c).1, T := T', nArr := σ.nArr,
        nSvc := Function.update σ.nSvc c (σ.nSvc c + 1),
        nUnif := (rosDepartPath u σ.nUnif σ.k c).2 }
  else { σ with time := σ.time + 1 }

/-- The ROS configuration with `N0 c` jobs of each type `c` at time `0`: the jobs are placed one
by one as arrivals (types in a fixed order), so every server with a nonempty queue is serving. -/
noncomputable def rosInit (K d : ℕ) (N0 : JobType K d → ℕ) : RosState K d :=
  (univ : Finset (JobType K d)).toList.foldl
    (fun k c => (fun k' => rosArrive K d k' c)^[N0 c] k) (rosEmpty K d)

/-- The sequence of post-event states of the ROS system started from `N0` at time `0`. -/
noncomputable def rosPath {K d : ℕ} (arr svc : JobType K d → ℕ → ℝ) (u : ℕ → ℝ)
    (N0 : JobType K d → ℕ) : ℕ → RosPathState K d
  | 0 => { time := 0, k := rosInit K d N0, T := 0, nArr := 0, nSvc := 0, nUnif := 0 }
  | j + 1 => rosPathStep arr svc u (rosPath arr svc u N0 j)

/-! ### The processes `N_c(t)`, `T_c(t)` and the fluid scaling -/

/-- The two service disciplines of §4.1. -/
inductive Policy
  | PS
  | ROS

open Classical in
/-- The index `j` of the inter-event interval `[time_j, time_{j+1})` containing `t`, given the
sequence of event times (`0` if `t` lies beyond every event time, a null event). -/
noncomputable def intervalIndex (times : ℕ → ℝ) (t : ℝ) : ℕ :=
  if h : ∃ j, t < times (j + 1) then Nat.find h else 0

/-- `(N_c(t), T_c(t))` of the system under `pol`, built from the primitives at the sample point
`ω`, started from `N0` at time `0`: piecewise constant `N`, piecewise linear `T`. -/
noncomputable def systemAt {K d : ℕ} {lam μ : ℝ} {Ω : Type*} [MeasureSpace Ω]
    (P : Primitives K d lam μ Ω) (pol : Policy) (N0 : JobType K d → ℕ) (ω : Ω) (t : ℝ) :
    (JobType K d → ℕ) × (JobType K d → ℝ) :=
  let arr := fun c i => P.arrClock c i ω
  let svc := fun c i => P.svcClock c i ω
  match pol with
  | Policy.PS =>
    let σ := psPath arr svc N0 (intervalIndex (fun j => (psPath arr svc N0 j).time) t)
    (σ.N, fun c => σ.T c + (t - σ.time) * psGrowth K d σ.N c)
  | Policy.ROS =>
    let u := fun i => P.unif i ω
    let σ := rosPath arr svc u N0 (intervalIndex (fun j => (rosPath arr svc u N0 j).time) t)
    (rosJobs K d σ.k, fun c => σ.T c + (t - σ.time) * rosGrowth K d σ.k c)

/-- The fluid-scaled number of type-`c` jobs `N_c^{r}(r t) / r` of (2), p. 6, for the system
with initial state `N_c^{r}(0) = ⌊r n_c(0)⌋`. -/
noncomputable def scaledN {K d : ℕ} {lam μ : ℝ} {Ω : Type*} [MeasureSpace Ω]
    (P : Primitives K d lam μ Ω) (pol : Policy) (n0 : JobType K d → ℝ) (r : ℝ) (ω : Ω)
    (c : JobType K d) (t : ℝ) : ℝ :=
  ((systemAt P pol (fun c' => ⌊r * n0 c'⌋₊) ω (r * t)).1 c : ℝ) / r

/-- The fluid-scaled cumulative capacity `T_c^{r}(r t) / r` spent on type `c`. -/
noncomputable def scaledT {K d : ℕ} {lam μ : ℝ} {Ω : Type*} [MeasureSpace Ω]
    (P : Primitives K d lam μ Ω) (pol : Policy) (n0 : JobType K d → ℝ) (r : ℝ) (ω : Ω)
    (c : JobType K d) (t : ℝ) : ℝ :=
  (systemAt P pol (fun c' => ⌊r * n0 c'⌋₊) ω (r * t)).2 c / r

/-- Convergence (3), p. 6, along the sequence `r`: for every type `c`, `N_c^{r_j}(r_j t)/r_j → n_c(t)`
and `T_c^{r_j}(r_j t)/r_j → τ_c(t)` uniformly on compact sets of `t ≥ 0` (u.o.c., footnote 1),
i.e. uniformly on `[0, T]` for every `T ≥ 0`. -/
def ConvergesUOC {K d : ℕ} {lam μ : ℝ} {Ω : Type*} [MeasureSpace Ω]
    (P : Primitives K d lam μ Ω) (pol : Policy) (n0 : JobType K d → ℝ) (ω : Ω) (r : ℕ → ℝ)
    (n τ : JobType K d → ℝ → ℝ) : Prop :=
  ∀ c (T : ℝ), 0 ≤ T →
    TendstoUniformlyOn (fun j t => scaledN P pol n0 (r j) ω c t) (n c) atTop (Set.Icc 0 T) ∧
    TendstoUniformlyOn (fun j t => scaledT P pol n0 (r j) ω c t) (τ c) atTop (Set.Icc 0 T)

/-- `(n, τ)` is a fluid limit of the system under `pol` with fluid initial state `n0` at the
sample point `ω`: the limit (3) along some sequence `r_j → ∞` of positive scalings. -/
def IsFluidLimitAt {K d : ℕ} {lam μ : ℝ} {Ω : Type*} [MeasureSpace Ω]
    (P : Primitives K d lam μ Ω) (pol : Policy) (n0 : JobType K d → ℝ) (ω : Ω)
    (n τ : JobType K d → ℝ → ℝ) : Prop :=
  ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Tendsto r atTop atTop ∧ ConvergesUOC P pol n0 ω r n τ

end RedundancyStab.IID


