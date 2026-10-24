-- Prove2me | Definitions.Def_LLMThroughput_TokenBudget_Model
-- name    : LLMThroughput_TokenBudget_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:43.15145+00:00
-- url     : https://prove2.me/theorems/87ca7c7b-7b84-40bd-8458-7967ca6dc6ab
-- title:
--   Basic LLM queueing model: batch time (4), Assumption 1, labelled state (5), feasible batches (6), dynamics (7) and steps 1–4, work-conserving (8)–(9), K-FCFS, i.i.d. arrivals (pp. 10–15, 37)
-- statement:
--   This file sets up the basic LLM queueing model of Dai, Deng, Li and Peng: a single GPU server that processes batches of prefill and decode tokens under a token budget.
--
--   **Batch processing time.** With nonnegative integers $c, a$ and a block size $b_0\ge 1$, a batch with token load $b$ takes
--   $$
--   t_b = c + a\left\lceil \frac{b}{b_0}\right\rceil
--   $$
--   time slots (eq. (4)). Assumption 1 asks that $b_0$ divide the token budget $b_{\max}\ge 1$; the theorems also assume $t_{b_{\max}}\ge 1$, so that the rate $b_{\max}/t_{b_{\max}}$ is defined.
--
--   **Requests and state.** Requests are labelled $0,1,2,\dots$ in order of global arrival. Each unfinished request $i$ carries its numbers $P_i$ of unprocessed prefill tokens and $D_i$ of unprocessed decode tokens. The state (eq. (5)) is
--   $$
--   X = \big(R, \{(P_i, D_i) : i\in Q\}\big),
--   $$
--   where $R$ is the remaining processing time of the current batch and $Q$ is the set of requests still in the system, listed in increasing label order. The state also records the label that the next arriving request will get. A state is *admissible* if:
--
--   1. labels increase and lie below that next label;
--   2. a request still in prefill ($P_i>0$) has $D_i\ge 1$;
--   3. when $R=0$ every request has $D_i\ge 1$;
--   4. at most $b_{\max}$ requests have $D_i=0$ (they wait for the current batch to finish).
--
--   **Scheduling algorithms.** A policy maps a state to a batch configuration $(\delta^p_i,\delta^d_i)_{i\in Q}$. It is a scheduling algorithm if at every admissible state with $R=0$ the configuration is feasible (eq. (6)):
--
--   1. $p_i>0 \Rightarrow \delta^d_i=0$;
--   2. $\delta^p_i\le p_i$;
--   3. $\delta^d_i\le 1$ and $\delta^d_i\le d_i$;
--   4. $\sum_i(\delta^p_i+\delta^d_i)=b\le b_{\max}$.
--
--   It is *work-conserving* if $\sum_i(\delta^p_i+\delta^d_i)=b_{\max}$ whenever the supply $\sum_i (p_i+\mathbf 1(p_i=0))$ is at least $b_{\max}$ (eqs. (8)–(9)). It satisfies *K-FCFS* if, whenever some request $j$ receives a decode token ($\delta^d_j>0$), every request $i$ still in the system with $i\le j-K$ receives at least one token ($\delta^p_i+\delta^d_i\ge 1$).
--
--   **Dynamics.** In every slot the following steps happen in order (p. 14):
--
--   1. *Scheduling.* If $R=0$ the policy chooses a batch, and its tokens are subtracted from the requests.
--   2. *Processing.* $R$ is updated by eq. (7): $R-1$ if $R>0$, $t_b-1$ if $R=0<t_b$, and $0$ if $R=0=t_b$.
--   3. *Departures.* If the batch finishes in this slot (the new $R$ is $0$ and the slot was not idle, i.e. $R>0$ or $t_b>0$), every request with no decode token left departs.
--   4. *Arrivals.* The slot's new requests join with their sizes.
--
--   The sample path is this recursion driven by the arrival counts $a_n$ and the sizes $(v_p(i),v_d(i))$ of the $i$-th arriving request. The file also defines:
--
--   - the total number of unprocessed tokens $|X|=\sum_{i\in Q}(P_i+D_i)$;
--   - the label-free configuration (remaining time and token counts in label order);
--   - the first time $n\ge 1$ at which the configuration lies in a set $F$;
--   - the cumulative phase-$f$ tokens $B_f(n)$ of the batches completed by time $n$;
--   - $E(n)=\sum_{m<n}a_m$.
--
--   **Randomness.** On a probability space, the arrival counts $\{a_n\}$ are i.i.d. and the sizes $\{(v_p(i),v_d(i))\}$ are i.i.d. The two sequences are independent of each other, all of these are measurable, $E[a_1]<\infty$, and $1\le v_p(i)\le v_p^{\max}$, $1\le v_d(i)\le v_d^{\max}$. The model's means are $\lambda=E[a_1]$, $m_p=E[v_p(1)]$ and $m_d=E[v_d(1)]$.
--
--   **Formalization Note** Slots and labels are 0-based: slot $n$ here is the paper's slot $n+1$. $\lceil b/b_0\rceil$ is the natural-number expression $(b+b_0-1)/b_0$. Natural subtractions are applied only where the operands are ordered for a scheduling algorithm. If a policy returns a configuration of the wrong length, the token update truncates the request list (junk); this cannot happen for a scheduling algorithm, whose configuration has one entry per request. The hitting time is in $\mathbb N\cup\{\infty\}$, with $\infty$ when $F$ is never reached. $B_f$ counts the tokens of batches formed during the run, at the end of the slot in which the batch completes. A batch formed in slot $m$ with $t_b>0$ completes at the end of slot $m+t_b-1$.
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, pp. 10–15, 37: eq. (4), Assumption 1 (p. 11), §3.1 (arrivals, state (5), feasibility (6), dynamics (7), steps 1–4), §3.2 (work-conserving (8)–(9), K-FCFS condition), App. B.1 (B_f, E(n), V_f)

import Mathlib

namespace LLMThroughput.TokenBudget

open MeasureTheory ProbabilityTheory

/-- Parameters of the batch processing time (4) and the token budget `b_max` (pp. 10–11).
Slots are integers (p. 13), so `t_0 = c` and `t_{b_0} − t_0 = a` are natural numbers. -/
structure Params where
  b0 : ℕ
  bmax : ℕ
  c : ℕ
  a : ℕ

/-- Batch processing time (4), p. 10: `t_b = c + a·⌈b/b_0⌉`, with `⌈b/b_0⌉ = (b + b_0 − 1)/b_0`
(natural-number division, exact for `b_0 ≥ 1`). -/
def Params.t (P : Params) (b : ℕ) : ℕ :=
  P.c + P.a * ((b + P.b0 - 1) / P.b0)

/-- Assumption 1 (p. 11) with the implicit nondegeneracy: `b_0 ≥ 1` divides `b_max ≥ 1`, and
`t_{b_max} ≥ 1` so that the rate `b_max/t_{b_max}` is defined. (`a, c ≥ 0` is built into `ℕ`.) -/
def Params.Valid (P : Params) : Prop :=
  1 ≤ P.b0 ∧ P.b0 ∣ P.bmax ∧ 1 ≤ P.bmax ∧ 1 ≤ P.t P.bmax

/-- An unfinished request: its global arrival label (0-based arrival index) and its numbers of
unprocessed prefill tokens `P_i` and decode tokens `D_i`. -/
structure Req where
  label : ℕ
  P : ℕ
  D : ℕ

/-- The labelled state (5), p. 13: the remaining time `R` of the current batch and the unfinished
requests, listed in increasing label order; `next` is the label the next arriving request gets. -/
structure State where
  R : ℕ
  reqs : List Req
  next : ℕ

/-- The empty system at time 0. -/
def State.empty : State := ⟨0, [], 0⟩

/-- A batch configuration `(δ^p_i, δ^d_i)_{i ∈ Q}`, one pair per request of `x.reqs`, in the same order. -/
abbrev Alloc := List (ℕ × ℕ)

/-- Token load `b = Σ_i (δ^p_i + δ^d_i)` of a batch configuration. -/
def load (δ : Alloc) : ℕ := (δ.map fun d => d.1 + d.2).sum

/-- Prefill tokens `Σ_i δ^p_i` of a batch configuration. -/
def prefillLoad (δ : Alloc) : ℕ := (δ.map Prod.fst).sum

/-- Decode tokens `Σ_i δ^d_i` of a batch configuration. -/
def decodeLoad (δ : Alloc) : ℕ := (δ.map Prod.snd).sum

/-- States the dynamics can produce (`X`, p. 13): labels strictly increasing and below `next`;
a request still in prefill has a decode token left; at a scheduling instant (`R = 0`) every request
has a decode token left; at most `b_max` requests wait, with no tokens left, for the current batch
to finish. -/
def Admissible (bmax : ℕ) (x : State) : Prop :=
  x.reqs.Pairwise (fun r s => r.label < s.label) ∧
  (∀ r ∈ x.reqs, r.label < x.next) ∧
  (∀ r ∈ x.reqs, 0 < r.P → 1 ≤ r.D) ∧
  (x.R = 0 → ∀ r ∈ x.reqs, 1 ≤ r.D) ∧
  (x.reqs.filter fun r => r.D = 0).length ≤ bmax

/-- Feasibility (6a)–(6d), p. 13, of a batch configuration in state `x`, plus `δ^d_i ≤ D_i`
(a request without decode tokens left contributes none). -/
def Feasible (bmax : ℕ) (x : State) (δ : Alloc) : Prop :=
  List.Forall₂ (fun r d => (0 < r.P → d.2 = 0) ∧ d.1 ≤ r.P ∧ d.2 ≤ 1 ∧ d.2 ≤ r.D) x.reqs δ ∧
  load δ ≤ bmax

/-- A policy maps the current labelled state to a batch configuration. -/
abbrev Policy := State → Alloc

/-- A (batch) scheduling algorithm (p. 14): feasible at every scheduling instant. -/
def IsScheduler (P : Params) (π : Policy) : Prop :=
  ∀ x, Admissible P.bmax x → x.R = 0 → Feasible P.bmax x (π x)

/-- Supply `Σ_{i∈Q} (p_i + 1(p_i = 0))` of the left side of (9), p. 15. -/
def supply (x : State) : ℕ := (x.reqs.map fun r => r.P + if r.P = 0 then 1 else 0).sum

/-- Work-conserving (8)–(9), p. 15: a full batch whenever the supply reaches `b_max`. -/
def IsWorkConserving (P : Params) (π : Policy) : Prop :=
  ∀ x, Admissible P.bmax x → x.R = 0 → P.bmax ≤ supply x → load (π x) = P.bmax

/-- The K-FCFS condition, p. 15: if request `j` gets a decode token, every request `i` still in
the system with `i ≤ j − K` (global arrival labels) gets at least one token. -/
def IsKFCFS (P : Params) (K : ℕ) (π : Policy) : Prop :=
  ∀ x, Admissible P.bmax x → x.R = 0 →
    ∀ p ∈ x.reqs.zip (π x), ∀ q ∈ x.reqs.zip (π x),
      0 < q.2.2 → p.1.label + K ≤ q.1.label → 1 ≤ p.2.1 + p.2.2

/-- Post-scheduling token counts `P'_i = P_i − δ^p_i`, `D'_i = D_i − δ^d_i` (step 1, p. 14). -/
def applyAlloc (reqs : List Req) (δ : Alloc) : List Req :=
  List.zipWith (fun r d => { r with P := r.P - d.1, D := r.D - d.2 }) reqs δ

/-- The batch configuration used in slot `n` from state `x`: `π x` if `R = 0`, none otherwise. -/
def batchOf (π : Policy) (x : State) : Alloc :=
  if x.R = 0 then π x else []

/-- One slot of the dynamics (steps 1–4, p. 14) from state `x`, the requests arriving in the slot
being `arr` (their (prefill, decode) sizes, in arrival order). -/
def step (P : Params) (π : Policy) (x : State) (arr : List (ℕ × ℕ)) : State :=
  let δ := batchOf π x
  let b := load δ
  -- 1. Scheduling
  let reqs' := if x.R = 0 then applyAlloc x.reqs δ else x.reqs
  -- 2. Processing, (7)
  let Rn := if 0 < x.R then x.R - 1 else if 0 < P.t b then P.t b - 1 else 0
  -- 3. Departures, at the end of a non-idle slot in which the batch finishes
  let done : Bool := decide ((0 < x.R ∨ 0 < P.t b) ∧ Rn = 0)
  let kept := if done then reqs'.filter (fun r => decide (r.D ≠ 0)) else reqs'
  -- 4. Arrivals, labelled `next, next + 1, …`
  let fresh := arr.mapIdx fun k s => ({ label := x.next + k, P := s.1, D := s.2 } : Req)
  { R := Rn, reqs := kept ++ fresh, next := x.next + arr.length }

/-- `E(n) = Σ_{m < n} a_m`, the number of requests arrived in slots `0, …, n − 1`. -/
def arrivalsBefore (a : ℕ → ℕ) (n : ℕ) : ℕ := ∑ m ∈ Finset.range n, a m

/-- Sizes of the requests arriving in slot `n`: requests number `E(n), …, E(n) + a_n − 1`. -/
def slotArrivals (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (a n)).map fun k => v (arrivalsBefore a n + k)

/-- The sample path: state at the beginning of slot `n` (0-based), started at `x`, with arrival
counts `a` and request sizes `v` (request number `i` of the run has sizes `v i`). -/
def run (P : Params) (π : Policy) (x : State) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ) : ℕ → State
  | 0 => x
  | n + 1 => step P π (run P π x a v n) (slotArrivals a v n)

/-- `|X(n)| = Σ_{i ∈ Q_n} (P_i(n) + D_i(n))`, p. 15. -/
def totalTokens (x : State) : ℕ := (x.reqs.map fun r => r.P + r.D).sum

/-- The label-free configuration of a state: remaining time and token counts in label order. -/
def config (x : State) : ℕ × List (ℕ × ℕ) := (x.R, x.reqs.map fun r => (r.P, r.D))

/-- First time `n ≥ 1` at which the configuration of the path lies in `F`; `⊤` if never. -/
noncomputable def hitTime (F : Finset (ℕ × List (ℕ × ℕ))) (path : ℕ → State) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ config (path n) ∈ F), (n : ℕ∞)

/-- Request with label `ℓ` has departed by state `x`: it has arrived and is no longer present. -/
def Departed (x : State) (ℓ : ℕ) : Prop := ℓ < x.next ∧ ∀ r ∈ x.reqs, r.label ≠ ℓ

/-- Request with label `ℓ` is in the system in state `x`. -/
def Present (x : State) (ℓ : ℕ) : Prop := ∃ r ∈ x.reqs, r.label = ℓ

/-- `B_f(n)`, p. 37: phase-`f` tokens (counted by `tok`) of the batches formed in slots `m < n` that
completed by time `n`; a batch of load `b` with `t_b > 0` formed in slot `m` completes at the end of slot
`m + t_b − 1`. -/
def completedTokens (P : Params) (π : Policy) (x : State) (a : ℕ → ℕ) (v : ℕ → ℕ × ℕ)
    (tok : Alloc → ℕ) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range n,
    if (run P π x a v m).R = 0 ∧ 0 < P.t (load (π (run P π x a v m))) ∧
        m + P.t (load (π (run P π x a v m))) ≤ n
    then tok (π (run P π x a v m)) else 0

/-- The i.i.d. arrival model of §3.1 (pp. 12–13) on a probability space: `a n` is the number of
requests arriving in slot `n`, `v i = (v_p(i), v_d(i))` the sizes of the `i`-th arriving request;
both sequences i.i.d., independent of each other, `E[a_1] < ∞`, sizes in `{1, …, v^max}`. -/
structure IIDArrivals {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (a : ℕ → Ω → ℕ)
    (v : ℕ → Ω → ℕ × ℕ) (vpmax vdmax : ℕ) : Prop where
  meas_a : ∀ n, Measurable (a n)
  meas_v : ∀ i, Measurable (v i)
  indep_a : iIndepFun a μ
  ident_a : ∀ n, IdentDistrib (a n) (a 0) μ μ
  indep_v : iIndepFun v μ
  ident_v : ∀ i, IdentDistrib (v i) (v 0) μ μ
  indep_av : IndepFun (fun ω n => a n ω) (fun ω i => v i ω) μ
  integrable_a : Integrable (fun ω => (a 0 ω : ℝ)) μ
  size_bounds : ∀ i ω, 1 ≤ (v i ω).1 ∧ (v i ω).1 ≤ vpmax ∧ 1 ≤ (v i ω).2 ∧ (v i ω).2 ≤ vdmax

/-- Arrival rate `λ = E[a_1]`. -/
noncomputable def arrivalRate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (a : ℕ → Ω → ℕ) : ℝ :=
  ∫ ω, (a 0 ω : ℝ) ∂μ

/-- Mean prefill length `m_p = E[v_p(1)]`. -/
noncomputable def meanPrefill {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (v : ℕ → Ω → ℕ × ℕ) : ℝ :=
  ∫ ω, ((v 0 ω).1 : ℝ) ∂μ

/-- Mean decode length `m_d = E[v_d(1)]`. -/
noncomputable def meanDecode {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (v : ℕ → Ω → ℕ × ℕ) : ℝ :=
  ∫ ω, ((v 0 ω).2 : ℝ) ∂μ

end LLMThroughput.TokenBudget


