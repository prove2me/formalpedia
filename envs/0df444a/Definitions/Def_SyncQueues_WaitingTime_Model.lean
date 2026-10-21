-- Prove2me | Definitions.Def_SyncQueues_WaitingTime_Model
-- name    : SyncQueues_WaitingTime_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:46.695268+00:00
-- url     : https://prove2.me/theorems/73da587c-bee0-4ad4-941d-edc166387875
-- title:
--   §2–§3 and §6, pp. 7–21 — the synchronized FCFS n-server queue with jobs of fixed size m, the tagged job's waiting time W^(n,t0), and the predecessor graph
-- statement:
--   This file fixes the queueing model of Section 2 for jobs of a fixed size $m$, the waiting time $W^{(n,t_0)}_\emptyset$ of Theorem 3.2, and the predecessor graph used in the proofs.
--
--   1. **The system.** There are $n\ge m$ identical servers. Jobs arrive as a Poisson process of rate $\lambda n$. Each job is split into $m$ pieces, routed to $m$ distinct servers with all $n!/(n-m)!$ assignments equally likely; piece $i$ has service requirement $\chi^{(i)}$, and the vector $(\chi^{(1)},\dots,\chi^{(m)})$ has a joint law $B_m$ on $[0,\infty)^m$ (the pieces of one job may be dependent). Inter-arrival gaps, routings and service vectors are all independent.
--   2. **Indexing.** Jobs are indexed backwards in time: job $0$ is the *tagged* job, the first arrival after time $0$, at time $E_0$; job $k\ge1$ is the $k$-th most recent arrival before $0$, at time $-(E_1+\dots+E_k)$. The gaps $E_0,E_1,\dots$ are i.i.d. $\mathrm{Exp}(\lambda n)$.
--   3. **Dynamics (Definition 2.1).** *Synchronization*: all pieces of a job start together, once each immediate predecessor (the previous job at each of its servers) has finished there. *Fairness*: each server is first come, first served. So if $F_s$ is the time at which server $s$ becomes free, a job arriving at $a$ with servers $s_1,\dots,s_m$ starts at
--   $$\max\{a,\ F_{s_1},\dots,F_{s_m}\},$$
--   and server $s_i$ is then busy until that start time plus $\chi^{(i)}$.
--   4. **The waiting time.** The system is empty at time $t_0<0$ (every server free at $t_0$); the jobs arriving in $(t_0,0]$ are served oldest first by the rule above, and $W^{(n,t_0)}_\emptyset$ is the start time of the tagged job minus its arrival time (waiting, excluding service).
--   5. **The piece law and the constants.** $B=\frac1m\sum_{i=1}^m\mathcal L(\chi^{(i)})$ is the law of a randomly chosen piece (p. 12 with $f_n=\delta_m$); $\lambda^*=\lambda m$ ((3.4)); and for $\beta>0$
--   $$\rho_\beta=m\,E\big[e^{\beta(\chi-\tau)}\big]=m\,E\big[e^{\beta\chi}\big]\,\frac{\lambda m}{\lambda m+\beta},\qquad \chi\sim B,\ \tau\sim\mathrm{Exp}(\lambda m)\ \text{independent}.$$
--   6. **The predecessor graph $\mathcal G_n(-\infty)$ (§2.1, §6).** The immediate predecessor of piece $i$ of a job is the most recent earlier job using the same server. Labels are words over $\{1,\dots,m\}$: $\emptyset$ is the tagged job, and $(\mathbf i,j)$ is the immediate predecessor of piece $j$ of the job labelled $\mathbf i$. Each edge carries $\hat X=\chi-\hat\tau$: the service requirement of the predecessor's piece in front, minus the inter-arrival time between the two jobs. Then $\hat S_{\mathbf j}=\hat X_{\mathbf j|1}+\dots+\hat X_{\mathbf j}$, $\hat S_\emptyset=0$,
--   $$\hat U_r=\max_{\mathbf j\in\hat A_r}\hat S_{\mathbf j},\qquad W^{(n)}=\bigvee_{r\ge0}\hat U_r,$$
--   and $M_r$ is the set of labels of length $r$ whose job also carries another label (Lemma 6.2).
--
--   These are the objects of Theorem 3.2 and of every milestone.
--
--   **Formalization Note** Only fixed job size $f_n=\delta_m$ is modelled (see the goal theorem for why). Servers are natural numbers and the $n$-system uses $\{0,\dots,n-1\}$; the routing law is the uniform law on injective maps $\{1,\dots,m\}\to\{0,\dots,n-1\}$, which is the zero measure when $n<m$, so every statement assumes $n\ge m$. A job is a triple (gap, routing, service vector); `IsSyncSystem` says these triples are independent over jobs with law $\mathrm{Exp}(\lambda n)\otimes\mathrm{Unif}\otimes B_m$. Jobs arriving after the tagged job cannot delay it (FCFS) and are not modelled. In $\mathcal G_n(-\infty)$ every piece has an immediate predecessor almost surely, so $\hat A_r$ is the set of all $m^r$ words of length $r$; on the null events where a set of arrivals in $(t_0,0]$ is infinite or a server is never used again, `Nat.card` and `sInf` return $0$. $W^{(n)}$ is a real supremum, meaningful when the $\hat U_r$ are bounded above, which every statement using it asserts or assumes. $\rho_\beta$ is an extended nonnegative real, infinite when $E[e^{\beta\chi}]=\infty$.
-- source:
--   Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, pp. 7–8, §2 and Definition 2.1; pp. 8–10, §2.1; pp. 10–12, (3.1)–(3.2), (3.4), the definition of $B$ on p. 12; pp. 20–21, §6 notation ($\hat U_r$, $\hat S_{\mathbf j}$, $W^{(n)}$); p. 25, Lemma 6.2 ($M_r$)

import Mathlib

namespace SyncQueues.WaitingTime

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ### The synchronized FCFS `n`-server queue with jobs of fixed size `m`

Olvera-Cravioto & Ruiz-Lacedelli, arXiv:1501.00186v3, §2 (pp. 7–8, Definition 2.1), (3.1)–(3.4)
(pp. 10–12) and the notation of §6 (pp. 20–21).

Servers are natural numbers; the `n`-server system only uses `{0, …, n-1}` (see `uniformInj`).
Jobs are indexed backwards in time: job `0` is the tagged job (the first arrival after time `0`),
job `k ≥ 1` is the `k`-th most recent arrival before time `0`. A job is a triple: arrival time, a
routing `ρ : Fin m → ℕ` (piece `i` goes to server `ρ i`) and a service vector `χ : Fin m → ℝ`. -/

/-- Start time of a job arriving at `a` with routing `ρ`, given the times `F s` at which each server
`s` becomes free: `max(a, max_i F(ρ i))`. Synchronization (all pieces start together, after all
immediate predecessors are done) and fairness (FCFS at every server), Definition 2.1. -/
noncomputable def startTime {m : ℕ} (F : ℕ → ℝ) (a : ℝ) (ρ : Fin m → ℕ) : ℝ :=
  max a (⨆ i : Fin m, F (ρ i))

/-- Server-free times after admitting the job `(a, ρ, χ)`: server `ρ i` is busy until
`start + χ i`; the other servers are unchanged. -/
noncomputable def admit {m : ℕ} (F : ℕ → ℝ) (a : ℝ) (ρ : Fin m → ℕ) (χ : Fin m → ℝ) : ℕ → ℝ :=
  fun s => if h : ∃ i, ρ i = s then startTime F a ρ + χ h.choose else F s

/-- Arrival times from the gaps `E`: the tagged job `0` arrives at `E 0 > 0`; job `k ≥ 1` arrives at
`-(E 1 + ⋯ + E k)`. -/
def arrival (E : ℕ → ℝ) (k : ℕ) : ℝ := if k = 0 then E 0 else -(∑ j ∈ Finset.Icc 1 k, E j)

/-- Server-free times just before the tagged job arrives, when the system is empty at time `t0`
(every server free at `t0`) and the jobs `K, K-1, …, 1` are admitted oldest first, each only if it
arrives after `t0`. -/
noncomputable def freeTimes {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ) (t0 : ℝ)
    (K : ℕ) : ℕ → ℝ :=
  ((List.range K).reverse).foldl
    (fun F j => if t0 < arrival E (j + 1) then
        admit F (arrival E (j + 1)) (R (j + 1)) (C (j + 1)) else F)
    (fun _ => t0)

/-- The number of jobs `k ≥ 1` arriving in `(t0, 0]`. (`Nat.card` is `0` if there are infinitely
many, which happens only on a null event.) -/
noncomputable def pastCount (E : ℕ → ℝ) (t0 : ℝ) : ℕ :=
  Nat.card {k : ℕ // 1 ≤ k ∧ t0 < arrival E k}

/-- `W^{(n,t0)}_∅`: the waiting time, excluding service, of the tagged job when the system starts
empty at time `t0 < 0`: its start time minus its arrival time. -/
noncomputable def waitT {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ) (t0 : ℝ) : ℝ :=
  startTime (freeTimes E R C t0 (pastCount E t0)) (arrival E 0) (R 0) - arrival E 0

/-- The uniform law on routings of the `m` pieces to `m` distinct servers among `{0, …, n-1}`
(all `n!/(n-m)!` assignments equally likely). It is the zero measure when `n < m`. -/
noncomputable def uniformInj (m n : ℕ) : Measure (Fin m → ℕ) :=
  uniformOn {ρ : Fin m → ℕ | Function.Injective ρ ∧ ∀ i, ρ i < n}

/-- `B`, the law of a randomly chosen piece: the average of the `m` coordinate marginals of the
joint service law `B_m` (p. 12, with `f_n = δ_m`). -/
noncomputable def pieceLaw {m : ℕ} (Bm : Measure (Fin m → ℝ)) : Measure ℝ :=
  (m : ℝ≥0∞)⁻¹ • ∑ i : Fin m, Bm.map (fun x => x i)

/-- The `n`-server system with jobs of size `m`, arrival rate `λn` and joint service law `B_m`:
the triples `(E k, R k, C k)` are mutually independent over `k`, and each has law
`Exp(λn) ⊗ uniformInj m n ⊗ B_m` (so within a job the gap, the routing and the service vector are
independent). The gaps `E k` are i.i.d. `Exp(λn)`: `E 0` is the time from `0` to the first arrival
after `0`, `E 1` the time from `0` back to the last arrival before `0`, and so on. -/
def IsSyncSystem {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m n : ℕ) (lam : ℝ)
    (Bm : Measure (Fin m → ℝ)) (E : ℕ → Ω → ℝ) (R : ℕ → Ω → (Fin m → ℕ))
    (C : ℕ → Ω → (Fin m → ℝ)) : Prop :=
  (∀ k, Measurable (E k) ∧ Measurable (R k) ∧ Measurable (C k)) ∧
  iIndepFun (fun k ω => (E k ω, R k ω, C k ω)) P ∧
  ∀ k, P.map (fun ω => (E k ω, R k ω, C k ω)) =
    (expMeasure (lam * n)).prod ((uniformInj m n).prod Bm)

/-- `ρ_β = E[N] E[e^{β(χ − τ)}] = m · E[e^{βχ}] · λ*/(λ* + β)` with `λ* = λm`, `χ ∼ B`,
`τ ∼ Exp(λ*)` independent, as an extended nonnegative real (it is `∞` when `E[e^{βχ}] = ∞`). -/
noncomputable def rho {m : ℕ} (Bm : Measure (Fin m → ℝ)) (lam beta : ℝ) : ℝ≥0∞ :=
  (m : ℝ≥0∞) * (∫⁻ x, ENNReal.ofReal (Real.exp (beta * x)) ∂(pieceLaw Bm)) *
    ENNReal.ofReal (lam * m / (lam * m + beta))

/-! ### The predecessor graph `G_n(−∞)` (§2.1, §3, §6) -/

/-- The immediate predecessor of piece `i` of job `k`: the most recent earlier job (a larger index)
that uses the server `R k i`. (`sInf ∅ = 0` only on the null event that no earlier job uses it.) -/
noncomputable def predJob {m : ℕ} (R : ℕ → Fin m → ℕ) (k : ℕ) (i : Fin m) : ℕ :=
  sInf {k' : ℕ | k < k' ∧ R k i ∈ Set.range (R k')}

/-- The piece of the immediate predecessor that sits in front of piece `i` of job `k`, i.e. the one
routed to the same server. -/
noncomputable def predPiece {m : ℕ} (R : ℕ → Fin m → ℕ) (k : ℕ) (i : Fin m) : Fin m :=
  if h : ∃ i', R (predJob R k i) i' = R k i then h.choose else i

/-- The edge weight `X̂ = χ − τ̂` from job `k` to the immediate predecessor of its piece `i`: the
service requirement of the predecessor's piece in front, minus the inter-arrival time between the
two jobs. -/
noncomputable def edgeHat {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ) (k : ℕ)
    (i : Fin m) : ℝ :=
  C (predJob R k i) (predPiece R k i) - (arrival E k - arrival E (predJob R k i))

/-- The job carrying the label `j` (root-first; `[]` is the tagged job `0`): follow the immediate
predecessors along the pieces `j_1, j_2, …`. -/
noncomputable def labelJob {m : ℕ} (R : ℕ → Fin m → ℕ) (j : List (Fin m)) : ℕ :=
  j.foldl (fun k i => predJob R k i) 0

/-- `Ŝ_j = X̂_{j|1} + X̂_{j|2} + ⋯ + X̂_j`, the sum of the edge weights along the path with label
`j` (`Ŝ_∅ = 0`). -/
noncomputable def pathSumHat {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ)
    (j : List (Fin m)) : ℝ :=
  (j.foldl (fun (st : ℕ × ℝ) i => (predJob R st.1 i, st.2 + edgeHat E R C st.1 i)) (0, 0)).2

/-- `Û_r = max_{j ∈ Â_r} Ŝ_j`, over the `m^r` labels at graph distance `r` from the tagged job
(`Û_0 = 0`). In `G_n(−∞)` every piece has an immediate predecessor, so `Â_r` is the set of all
words of length `r`. -/
noncomputable def Uhat {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ) (r : ℕ) : ℝ :=
  ⨆ v : Fin r → Fin m, pathSumHat E R C (List.ofFn v)

/-- `⋁_{r=0}^{k} Û_r`. -/
noncomputable def UhatUpTo {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ) (k : ℕ) :
    ℝ :=
  (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one (fun r => Uhat E R C r)

/-- `W^{(n)} = ⋁_{r ≥ 0} Û_r` (p. 21). A real supremum: it is the true supremum when the `Û_r`
are bounded above, which every statement that uses it asserts or assumes. -/
noncomputable def Wn {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ) : ℝ :=
  ⨆ r : ℕ, Uhat E R C r

/-- `M_r` of Lemma 6.2: the labels at graph distance `r` whose job also carries some other label
(of any length). -/
noncomputable def multiLabelled {m : ℕ} (R : ℕ → Fin m → ℕ) (r : ℕ) : Finset (Fin r → Fin m) := by
  classical
  exact Finset.univ.filter fun v =>
    ∃ j : List (Fin m), j ≠ List.ofFn v ∧ labelJob R j = labelJob R (List.ofFn v)

end SyncQueues.WaitingTime


