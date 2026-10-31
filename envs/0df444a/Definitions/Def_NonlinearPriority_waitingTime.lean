-- Prove2me | Definitions.Def_NonlinearPriority_waitingTime
-- name    : NonlinearPriority_waitingTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:04.824539+00:00
-- url     : https://prove2.me/theorems/bc71958f-12fb-4c1b-9105-0673d44d6f08
-- title:
--   Sample path of a fixed-priority policy and the waiting time $V^{\pi,x_0}_n$
-- statement:
--   A fixed-priority policy of the class $\Pi^F$ is described by its priority-order map $\mathrm{ord}:\{1,\dots,K\}\to\mathbb N$: a smaller order is served first, and customers whose types have the same order are served first-come-first-served. The server is nonidling and nonpreemptive.
--
--   Given an initial state $x_0$ (a finite queue of customers with types and service times, plus the residual service time of a customer in service) and a realization of the arrival stream (interarrival times, types, service times), the sample path is built over successive service starts. If the server frees at time $F$ and some customer that has not started is present, the next service starts at $F$; otherwise it starts at the arrival time of the next customer. The customer started is, among those present and not yet started, the one with the least order, and among those the earliest. The waiting time of arrival $n$ is
--   $$V^{\pi,x_0}_n=(\text{start of its service})-T_n.$$
--
--   **Formalization Note** Customers are numbered with the initial queue first and arrivals after it; FCFS ties are broken by this number, which is arrival order whenever interarrival times are nonnegative. An arrival that is never started gets the junk waiting time $0$; when $\rho<1$ this happens with probability zero. Every waiting time is nonnegative.
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, §3, pp.3–4 (PDF 4–5); (1), p.4 (PDF 5)

import Mathlib

namespace NonlinearPriority

/-- **An initial state** of the queue (the `x0` of (1), p. 4, PDF 5). Ouyang, Argon and Ziya,
Management Science (2021), doi:10.1287/mnsc.2020.3952.

A finite list of customers waiting at time `0`, each with its type and its service time `≥ 0`
(FCFS rank = list position, all ahead of every later arrival), and the residual service time
`residual ≥ 0` of a customer in service at time `0` (the server is busy on `[0, residual)`). The
empty system is `queue = []`, `residual = 0`.

**Formalization Note.** The paper names the initial state `x0` without describing it; this is the
general state of a nonpreemptive single-server queue at a time when no service is in progress
other than the residual one. -/
structure InitState (K : ℕ) where
  /-- customers waiting at time `0`: type and service time -/
  queue : List (Fin K × ℝ)
  /-- residual service time of the customer in service at time `0` -/
  residual : ℝ
  queue_nonneg : ∀ c ∈ queue, 0 ≤ c.2
  residual_nonneg : 0 ≤ residual

/-- **A realization of the arrival stream**: interarrival times `a n`, types `y n` and service
times `sv n` of the arrivals `n = 0, 1, 2, …`; arrival `n` happens at `a 0 + ⋯ + a n`. -/
structure Realization (K : ℕ) where
  /-- interarrival times -/
  a : ℕ → ℝ
  /-- types of the arrivals -/
  y : ℕ → Fin K
  /-- service times of the arrivals -/
  sv : ℕ → ℝ

variable {K : ℕ}

/-- The arrival time `a 0 + ⋯ + a n` of arrival `n`. -/
def arrTime (r : Realization K) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), r.a j

/-- Customers are numbered by `ℕ`: `c < L` (with `L` the length of the initial queue) is the
initial customer at list position `c`, and `c ≥ L` is arrival `c - L`. In this numbering FCFS is
the order of `ℕ`. The type of customer `c`. -/
def custType (x0 : InitState K) (r : Realization K) (c : ℕ) : Fin K :=
  if h : c < x0.queue.length then (x0.queue.get ⟨c, h⟩).1 else r.y (c - x0.queue.length)

/-- The service time of customer `c`. -/
def custService (x0 : InitState K) (r : Realization K) (c : ℕ) : ℝ :=
  if h : c < x0.queue.length then (x0.queue.get ⟨c, h⟩).2 else r.sv (c - x0.queue.length)

/-- Customer `c` is in the system at time `t` (or was before): initial customers always are,
arrival `n` from its arrival time on. -/
def Present (x0 : InitState K) (r : Realization K) (c : ℕ) (t : ℝ) : Prop :=
  c < x0.queue.length ∨ arrTime r (c - x0.queue.length) ≤ t

open Classical in
/-- The time of the next service start when the server frees at `F` and the customers in `St`
have already started: `F` if some customer that has not started is present at `F` (nonidling);
otherwise the arrival time of the first customer that has not started. -/
noncomputable def nextStart (x0 : InitState K) (r : Realization K) (F : ℝ) (St : Finset ℕ) : ℝ :=
  if ∃ c, c ∉ St ∧ Present x0 r c F then F
  else arrTime r (sInf {c | c ∉ St} - x0.queue.length)

/-- The customer that starts service at time `s` when the customers in `St` have started: among
the present customers that have not started, the least priority order `ord (type)` (a smaller
order is served first), and among those the first in FCFS order. -/
noncomputable def select (x0 : InitState K) (r : Realization K) (ord : Fin K → ℕ) (s : ℝ)
    (St : Finset ℕ) : ℕ :=
  sInf {c | c ∉ St ∧ Present x0 r c s ∧
    ord (custType x0 r c) = sInf {o | ∃ d, d ∉ St ∧ Present x0 r d s ∧ ord (custType x0 r d) = o}}

/-- The state after `m` service starts: the time `Fₘ` at which the server frees and the set of
customers that have started. `F₀` is the residual service time of the initial state. -/
noncomputable def state (x0 : InitState K) (r : Realization K) (ord : Fin K → ℕ) :
    ℕ → ℝ × Finset ℕ
  | 0 => (x0.residual, ∅)
  | m + 1 =>
    let s := nextStart x0 r (state x0 r ord m).1 (state x0 r ord m).2
    let c := select x0 r ord s (state x0 r ord m).2
    (s + custService x0 r c, insert c (state x0 r ord m).2)

/-- The time of the `m`th service start (`m = 0, 1, …`, counting from time `0`). -/
noncomputable def startTime (x0 : InitState K) (r : Realization K) (ord : Fin K → ℕ) (m : ℕ) :
    ℝ :=
  nextStart x0 r (state x0 r ord m).1 (state x0 r ord m).2

/-- The customer whose service starts `m`th. -/
noncomputable def startedCust (x0 : InitState K) (r : Realization K) (ord : Fin K → ℕ) (m : ℕ) :
    ℕ :=
  select x0 r ord (startTime x0 r ord m) (state x0 r ord m).2

open Classical in
/-- **The queue waiting time of arrival `n`** under the fixed priority policy `ord`
(§3, pp. 3–4, PDF 4–5; the `V^{π,x0}_{i,k}` of (1)). Ouyang, Argon and Ziya, Management Science
(2021), doi:10.1287/mnsc.2020.3952.

The policy is given by its priority-order map `ord : Fin K → ℕ`: a smaller order is served first,
types with the same order are served FCFS (the class `Π^F`). The server is nonidling and
nonpreemptive: when it frees (or when the first customer arrives to an empty system) it starts the
present customer with the least order, the earliest among those. The waiting time of arrival `n`
is the start of its service minus its arrival time.

**Formalization Note.**
* The sample path is the recursion `state` over successive service starts.
* Ties: within one order, FCFS by customer number (initial customers first, in list order, then
  arrivals by index), which is arrival order whenever interarrival times are `≥ 0`.
* Junk value: an arrival that is never started gets waiting time `0`. When `ρ < 1` every customer
  is served with probability one, so the junk value is never used on a set of positive
  probability.
* Every waiting time is `≥ 0`: a customer starts only when present. -/
noncomputable def waitingTime {K : ℕ} (x0 : InitState K) (r : Realization K) (ord : Fin K → ℕ)
    (n : ℕ) : ℝ :=
  if h : ∃ m, startedCust x0 r ord m = x0.queue.length + n then
    startTime x0 r ord (Nat.find h) - arrTime r n
  else 0

end NonlinearPriority


