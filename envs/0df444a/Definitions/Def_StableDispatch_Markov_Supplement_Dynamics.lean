-- Prove2me | Definitions.Def_StableDispatch_Markov_Supplement_Dynamics
-- name    : StableDispatch_Markov_Supplement_Dynamics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:43:49.302476+00:00
-- url     : https://prove2.me/theorems/d173493c-693c-4681-b230-d86e509175c0
-- title:
--   §2.1, §2.3.1–§2.4, pp. 5, 7–12 — primitives, the sample-path construction of (Q, M, Z), the average message rate (2.2) and the stability region Γn(λ)
-- statement:
--   **Primitives (§2.1, §2.3.1).** An interarrival law of rate $\lambda n$ is a probability law $F$ on $[0,\infty)$ with finite mean $1/(\lambda n)$; a job-size law is a probability law $\nu$ on $[0,\infty)$ with mean one.
--
--   **States.** A state $(\mathbf Q,M,Z)$ consists of $n$ workload sequences, a memory state and the time $Z$ since the previous arrival. The **state space** is the set of states in which every queue holds finitely many jobs (positive workloads on an initial segment, zeros after), $Z\ge0$ and $F((Z,\infty))>0$.
--
--   **Fundamental processes.** From a state with age $z$, the fundamental processes are independent: interarrival times, the first equal to the residual $\tau-z$ of $\tau\sim F$ conditioned on $\tau>z$ and the others i.i.d. $F$; i.i.d. exponential interevent times of rate $\beta_n$ (the Poisson process $R_n$); i.i.d. job sizes $\sim\nu$; and eight i.i.d. uniform $[0,1]$ sequences $U_{1,k},\dots,U_{8,k}$.
--
--   **Sample paths (§2.3.2).** Between events each busy server $i$ reduces the workload of its head job at rate $\mu_i$ and $Z$ grows at unit rate. At the $k$-th arrival, of size $W_k$: $S_k=f_1(M,W_k,U_{1,k})$, $D_k=f_2(M,W_k,\{(Q_i,\mu_i,i):i\in S_k\},U_{2,k})$, the job joins the end of queue $D_k$, $M\leftarrow f_3(\dots,D_k,U_{3,k})$ and $Z\leftarrow0$. At the $k$-th event of $R_n$: if $i=g_1(\mathbf Q,\mu,U_{4,k})\neq0$, then $S^s_k=g_2(M,i,Q_i,\mu_i,U_{5,k})$ and $M\leftarrow g_3(M,i,Q_i,\mu_i,\{(Q_j,\mu_j,j):j\in S^s_k\},U_{6,k})$. At the $k$-th departure from server $i$: if $h_1(Q_i,\mu_i,U_{7,k})=1$ then $M\leftarrow h_2(M,i,Q_i,\mu_i,U_{8,k})$. The path $t\mapsto(\mathbf Q(t),M(t),Z(t))$ is right-continuous.
--
--   **Average message rate (2.2).**
--
--   $$\limsup_{t\to\infty}\frac1t\Big[\sum_{k=1}^{A_n(t)}2|S_k|+\sum_{k=1}^{R_n(t)}\big(1+2|S^s_k|\big)\mathbf 1\{g_1(\dots)\ne0\}+\sum_{i=1}^n\sum_{k:\,T^d_k(i)<t}\mathbf 1\{h_1(\dots)=1\}\Big]\in[0,\infty].$$
--
--   A policy's message rate is **bounded by $\alpha$ almost surely** if this lim sup is at most $\alpha$ almost surely, for every $\mu\in\Sigma_n$ and every initial state of the state space.
--
--   **Stability region (§2.4).** $\Gamma_n(\lambda)$ is the set of $\mu\in\Sigma_n$ for which the process family $(\mathbf Q,M,Z)$ is positive Harris recurrent on the state space.
--
--   These are the objects in the statement of Theorem 2.2.
--
--   **Formalization Note** At simultaneous events, departures (in increasing server index) are processed before arrivals, and arrivals before events of $R_n$. A job of size $0$ departs at its arrival instant. $U_{7,k},U_{8,k}$ are used at the $k$-th departure of each server. The conditioning of the first interarrival time on $\tau>z$ is the delay that makes $(\mathbf Q,M,Z)$ Markov; states with $F((z,\infty))=0$ cannot occur and are excluded from the state space. If infinitely many events occur before a finite time (a null event), the path is set to its initial state. $\Sigma_n$ is the published `StableDispatch.Markov.Sigma`.
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, p. 5, §2.1 and (2.1); pp. 7–10, §2.3.1–§2.3.2; p. 11, (2.2); pp. 11–12, §2.4

import Mathlib
import Definitions.Def_MatrixAnalytic_Tree_Process
import Definitions.Def_StableDispatch_Markov_Setting
import Definitions.Def_StableDispatch_Markov_Supplement_Harris
import Definitions.Def_StableDispatch_Markov_Supplement_Policy

namespace StableDispatch.Markov.Supplement

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

noncomputable section

open Classical

/-- The interarrival law of a renewal arrival process of rate `λn` (§2.1, §2.3.1): a probability
law on `[0, ∞)` with finite mean `1/(λn)`. -/
def IsInterarrivalLaw (lam : ℝ) (n : ℕ) (F : Measure ℝ) : Prop :=
  IsProbabilityMeasure F ∧ F (Iio 0) = 0 ∧ Integrable (fun x => x) F ∧
    ∫ x, x ∂F = 1 / (lam * n)

/-- A job-size law (§2.1): a probability law on `[0, ∞)` with mean one. -/
def IsJobSizeLaw (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ν (Iio 0) = 0 ∧ Integrable (fun x => x) ν ∧ ∫ x, x ∂ν = 1

/-- A state `(Q, M, Z)` of the process of §2.3.2: the workload sequences of the `n` queues, the
memory state, and the time `Z` elapsed since the previous arrival. -/
abbrev SysState (n m : ℕ) := (Fin n → Queue) × Fin m × ℝ

/-- A queue holding finitely many jobs: positive workloads on an initial segment, zeros after. -/
def IsFiniteQueue (q : Queue) : Prop :=
  ∃ L : ℕ, (∀ k < L, 0 < q k) ∧ ∀ k, L ≤ k → q k = 0

/-- The state space on which recurrence is asked: every queue holds finitely many jobs, and the
age `Z ≥ 0` is one the arrival process can have (an interarrival time exceeds `Z` with positive
probability). -/
def stateSpace (n m : ℕ) (F : Measure ℝ) : Set (SysState n m) :=
  {x | (∀ i, IsFiniteQueue (x.1 i)) ∧ 0 ≤ x.2.2 ∧ 0 < F (Ioi x.2.2)}

/-- Realizations of the fundamental processes (§2.3.1): interarrival times (entry `0` is the
time of the first arrival), interevent times of the spontaneous-message process `R_n`, job sizes
`W_k`, and the eight randomization sequences (`ω.2.2.2 j k = U_{j+1,k}`). All sequences are
indexed from `0`. -/
abbrev Fund := (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) × (Fin 8 → ℕ → ℝ)

/-- The law of the fundamental processes started from age `z`: independent interarrival times,
the first distributed as the residual `τ − z` of an interarrival time `τ ~ F` conditioned on
`τ > z` (the delay of the delayed renewal process `A_n`) and the others `~ F`; i.i.d.
exponential interevent times of rate `β` (so `R_n` is Poisson of rate `β`); i.i.d. job sizes
`~ ν`; and i.i.d. uniform `[0, 1]` randomization variables; all independent. -/
def fundLaw (F ν : Measure ℝ) (β z : ℝ) : Measure Fund :=
  (Measure.infinitePi fun k : ℕ =>
      if k = 0 then (cond F (Ioi z)).map (fun y => y - z) else F).prod
    ((Measure.infinitePi fun _ : ℕ => expMeasure β).prod
      ((Measure.infinitePi fun _ : ℕ => ν).prod
        (Measure.infinitePi fun _ : Fin 8 => Measure.infinitePi fun _ : ℕ => unif)))

/-- Time of the `k`-th arrival (`0`-based), `T_{k+1}` in the paper. -/
def arrivalTime (ω : Fund) (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), ω.1 i

/-- Time of the `k`-th event of `R_n` (`0`-based), `T^s_{k+1}` in the paper. -/
def msgTime (ω : Fund) (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), ω.2.1 i

/-- Number of jobs in a finite queue (index of its first zero entry). -/
def qlen (q : Queue) : ℕ := if h : ∃ k, q k = 0 then Nat.find h else 0

/-- Append a job of workload `w` at the end of the queue. -/
def append (q : Queue) (w : ℝ) : Queue := Function.update q (qlen q) w

/-- Remove the job at the head of the queue. -/
def shiftQ (q : Queue) : Queue := fun k => q (k + 1)

/-- The configuration of the event-driven construction after some events: current time, state
`(Q, M, Z)`, numbers of arrivals, `R_n`-events and departures (per server) processed so far, a
zero-size job awaiting its instantaneous departure, and the number of messages exchanged at the
last event together with whether that event was a departure. -/
structure Config (n m : ℕ) where
  time : ℝ
  Q : Fin n → Queue
  M : Fin m
  Z : ℝ
  na : ℕ
  ns : ℕ
  nd : Fin n → ℕ
  zeroJob : Option (Fin n)
  weight : ℕ
  isDep : Bool

variable {n : ℕ} (P : Policy n) (μ : Fin n → ℝ) (ω : Fund)

/-- Let time run for `s`: each server works on its head-of-line job at rate `μ_i`, and `Z` grows
at unit rate. -/
def advance (c : Config n P.memSize) (s : ℝ) : Config n P.memSize :=
  { c with time := c.time + s
           Q := fun i => Function.update (c.Q i) 0 (max (c.Q i 0 - μ i * s) 0)
           Z := c.Z + s }

/-- A departure from server `i`, leaving queue state `qi` (§2.3.2, service completions): server
`i` messages iff `h1(Q_i, μ_i, U_7) = 1`, in which case the memory becomes
`h2(M, i, Q_i, μ_i, U_8)`; `U_7, U_8` are indexed by the departure count of server `i`. -/
def depart (c : Config n P.memSize) (i : Fin n) (qi : Queue) : Config n P.memSize :=
  let k := c.nd i
  let msg := P.h1 qi (μ i) (ω.2.2.2 6 k)
  { c with Q := Function.update c.Q i qi
           M := if msg then P.h2 c.M i qi (μ i) (ω.2.2.2 7 k) else c.M
           nd := Function.update c.nd i (k + 1)
           zeroJob := none
           weight := if msg then 1 else 0
           isDep := true }

/-- The arrival of the next job (§2.3.2, job arrivals): `S = f1(M, W, U_1)`,
`D = f2(M, W, {(Q_i, μ_i, i) : i ∈ S}, U_2)`, the job joins the end of queue `D`,
`M ← f3(M, W, {…}, D, U_3)`, `Z ← 0`; `2|S|` messages are exchanged. A job of size `0` departs
at its arrival instant (it is recorded as a pending zero-size departure from `D`). -/
def arrive (c : Config n P.memSize) : Config n P.memSize :=
  let k := c.na
  let w := ω.2.2.1 k
  let S := P.f1 c.M w (ω.2.2.2 0 k)
  let I := info S c.Q μ
  let D := P.f2 c.M w I (ω.2.2.2 1 k)
  { c with Q := if 0 < w then Function.update c.Q D (append (c.Q D) w) else c.Q
           M := P.f3 c.M w I D (ω.2.2.2 2 k)
           Z := 0
           na := k + 1
           zeroJob := if 0 < w then none else some D
           weight := 2 * S.card
           isDep := false }

/-- An event of `R_n` (§2.3.2, spontaneous messages): server `i = g1(Q, μ, U_4)` messages (none if
`g1 = 0`); then `S = g2(M, i, Q_i, μ_i, U_5)` and `M ← g3(M, i, Q_i, μ_i, {…}, U_6)`;
`1 + 2|S|` messages are exchanged. -/
def spont (c : Config n P.memSize) : Config n P.memSize :=
  let k := c.ns
  match P.g1 c.Q μ (ω.2.2.2 3 k) with
  | none => { c with ns := k + 1, zeroJob := none, weight := 0, isDep := false }
  | some i =>
    let S := P.g2 c.M i (c.Q i) (μ i) (ω.2.2.2 4 k)
    { c with M := P.g3 c.M i (c.Q i) (μ i) (info S c.Q μ) (ω.2.2.2 5 k)
             ns := k + 1
             zeroJob := none
             weight := 1 + 2 * S.card
             isDep := false }

/-- Process the next event. A pending zero-size departure comes first; otherwise the earliest
of: the next departure (head workload `Q_i(0)` finishes after `Q_i(0)/μ_i`), the next arrival, the
next `R_n`-event. Ties: departures before arrivals before `R_n`-events, departures in increasing
server index. -/
def step (c : Config n P.memSize) : Config n P.memSize :=
  match c.zeroJob with
  | some d => depart P μ ω c d (c.Q d)
  | none =>
    let TA := arrivalTime ω c.na
    let TS := msgTime ω c.ns
    let isNext : Fin n → Prop := fun i => 0 < c.Q i 0 ∧ c.time + c.Q i 0 / μ i ≤ TA ∧
      c.time + c.Q i 0 / μ i ≤ TS ∧ ∀ j, 0 < c.Q j 0 → c.Q i 0 / μ i ≤ c.Q j 0 / μ j
    if h : ∃ i, isNext i then
      let i := Fin.find isNext h
      let c' := advance P μ c (c.Q i 0 / μ i)
      depart P μ ω c' i (shiftQ (c'.Q i))
    else if TA ≤ TS then arrive P μ ω (advance P μ c (TA - c.time))
    else spont P μ ω (advance P μ c (TS - c.time))

/-- The configuration after `k` events, started at time `0` in state `x`. -/
def config (x : SysState n P.memSize) : ℕ → Config n P.memSize
  | 0 => { time := 0, Q := x.1, M := x.2.1, Z := x.2.2, na := 0, ns := 0, nd := fun _ => 0,
           zeroJob := none, weight := 0, isDep := false }
  | k + 1 => step P μ ω (config x k)

/-- The sample path `t ↦ (Q(t), M(t), Z(t))` (càdlàg): the state after every event of time `≤ t`,
advanced to time `t`. (If events accumulate before `t`, a null event, the value is `x`.) -/
def path (x : SysState n P.memSize) (t : ℝ) : SysState n P.memSize :=
  if h : ∃ k, t < (config P μ ω x (k + 1)).time then
    let c := advance P μ (config P μ ω x (Nat.find h))
      (t - (config P μ ω x (Nat.find h)).time)
    (c.Q, c.M, c.Z)
  else x

/-- The number of messages exchanged up to time `t`, the bracket of (2.2): `2|S_k|` for every
arrival with `T_k ≤ t`, `(1 + 2|S^s_k|)` for every event of `R_n` with `T^s_k ≤ t` at which a
server messages, and `1` for every departure at a time `< t` at which the server messages. -/
def msgCount (x : SysState n P.memSize) (t : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ,
    if ((config P μ ω x (k + 1)).isDep = true ∧ (config P μ ω x (k + 1)).time < t) ∨
        ((config P μ ω x (k + 1)).isDep = false ∧ (config P μ ω x (k + 1)).time ≤ t) then
      ((config P μ ω x (k + 1)).weight : ℝ≥0∞)
    else 0

/-- The average message rate (2.2), p. 11: `limsup_{t → ∞} (1/t)·(messages up to t)`, in
`[0, ∞]`. -/
def avgMessageRate (x : SysState n P.memSize) : ℝ≥0∞ :=
  limsup (fun t : ℝ => msgCount P μ ω x t / ENNReal.ofReal t) atTop

variable {P μ ω}

/-- The average message rate of the policy is at most `α` almost surely: for every rate vector
`μ ∈ Σ_n` and every initial state, under the given primitives. -/
def MessageRateBounded (P : Policy n) (F ν : Measure ℝ) (α : ℝ) : Prop :=
  ∀ μ ∈ StableDispatch.Markov.Sigma n, ∀ x ∈ stateSpace n P.memSize F,
    ∀ᵐ ω ∂(fundLaw F ν P.beta x.2.2), avgMessageRate P μ ω x ≤ ENNReal.ofReal α

/-- The stability region `Γ_n(λ)` of a policy (§2.4, pp. 11–12), for the arrival process with
interarrival law `F` (rate `λn`) and job-size law `ν`: the rate vectors `μ ∈ Σ_n` for which the
process `(Q(·), M(·), Z(·))` is positive Harris recurrent on the state space. -/
def stabilityRegion (P : Policy n) (F ν : Measure ℝ) : Set (Fin n → ℝ) :=
  {μ | μ ∈ StableDispatch.Markov.Sigma n ∧
    IsPositiveHarris (stateSpace n P.memSize F) (fun x => fundLaw F ν P.beta x.2.2)
      (fun x ω t => path P μ ω x t)}

end

end StableDispatch.Markov.Supplement


