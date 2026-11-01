-- Prove2me | Definitions.Def_PerfCorrMSQ_FifoAbandon
-- name    : PerfCorrMSQ_FifoAbandon
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:47.320623+00:00
-- url     : https://prove2.me/theorems/216c379a-95a7-438d-8b8c-5c1b5a375846
-- title:
--   FIFO non-idling $n$-server queue with abandonment from the queue: the sample-path recursion
-- statement:
--   A FIFO many-server queue with abandonment, on one sample path. Customers are indexed by $c=0,1,2,\dots$ in the order in which they are served (FIFO). Customer $c$ joins the queue at time $a_c$, abandons at its deadline $d_c$ unless it has entered service before, and, if served, occupies one server for $\sigma_c$ time units. The state seen by customer $c$ is the sorted list $V_c$ of the times at which the $n$ servers become free, starting from a given list $V_0$.
--
--   Customer $c$ can start service at
--
--   $$
--   s_c=\max\big(a_c,\ \min V_c\big).
--   $$
--
--   It is **served** iff $s_c<d_c$; then the earliest free time in $V_c$ is replaced by $s_c+\sigma_c$. Otherwise it abandons at $d_c$ and $V_{c+1}=V_c$. The time customer $c$ leaves the queue is $s_c$ if served and $d_c$ otherwise; it leaves the system at $s_c+\sigma_c$ if served and at $d_c$ otherwise.
--
--   This is the generic $G/G/n+G$ FIFO recursion; with nondecreasing $a_c$ and a sorted initial list it is non-idling (a server never idles while a customer waits) and a customer who abandons never occupies a server.
--
--   **Formalization Note** The tie $s_c=d_c$ counts as abandonment; for continuous patience laws this is a null event. With $n=0$ servers nobody is served. Two structural lemmas record $a_c\le s_c<d_c$ for served customers.
-- source:
--   Yu and Perry, Many-Server Heavy-Traffic Limits for Queueing Systems with Perfectly Correlated Service and Patience Times, arXiv:2008.12890v1, §2, p.4 (FIFO service, abandonment from the queue)

import Mathlib

open scoped NNReal

namespace PerfCorrMSQ

/-!
The FIFO, non-idling `n`-server queue with abandonment from the queue, as a deterministic
recursion on one sample path (Yu–Perry, arXiv:2008.12890v1, §2, p.4: "A customer begins service
with an agent immediately upon arrival, if an idle agent is available, and otherwise, waits in the
queue for his turn to enter service … customers are served in accordance with the FIFO discipline
… if a customer runs out of patience before his turn to enter service, that customer abandons the
queue without returning").

Customers are indexed by `c : ℕ` in FIFO order. Customer `c` joins the queue at time `a c`,
abandons at its deadline `d c` unless it has entered service before, and, if served, occupies
one server for `σ c` time units. The server state is the sorted list of the times at which the
servers become free; it has one entry per server.

**Formalization Note.** Customer `c` enters service at `max (a c) v`, where `v` is the earliest
free time among the servers left by customers `0, …, c − 1`, provided `max (a c) v < d c`
(tie convention: a customer whose patience expires exactly when a server frees abandons; for
continuous patience laws this is a null event). Otherwise it abandons and never occupies a server.
With `n = 0` servers nobody is served. The recursion is FIFO and non-idling when the `a c` are
nondecreasing in `c` and the initial list is sorted.
-/

/-- One step of the FIFO recursion. Given the sorted list of server free times, a customer with
arrival time `a`, deadline `d` and service requirement `σ` enters service at `max a v` (`v` the
head of the list, the earliest free time) if `max a v < d`; the server is then free again at
`max a v + σ`, inserted in order. Otherwise (or if there is no server) the customer abandons and
the list is unchanged. The first component is the service-start time, if any. -/
noncomputable def serveStep (a d σ : ℝ) : List ℝ → Option ℝ × List ℝ
  | [] => (none, [])
  | v :: L =>
    if max a v < d then (some (max a v), L.orderedInsert (· ≤ ·) (max a v + σ))
    else (none, v :: L)

/-- The sorted list of server free times seen by customer `c`, i.e. after customers
`0, …, c − 1` have been processed, starting from the list `init` at time `0`. -/
noncomputable def freeTimes (init : List ℝ) (a d σ : ℕ → ℝ) : ℕ → List ℝ
  | 0 => init
  | c + 1 => (serveStep (a c) (d c) (σ c) (freeTimes init a d σ c)).2

/-- The service-start time of customer `c` (`none` if `c` abandons). -/
noncomputable def startTime (init : List ℝ) (a d σ : ℕ → ℝ) (c : ℕ) : Option ℝ :=
  (serveStep (a c) (d c) (σ c) (freeTimes init a d σ c)).1

/-- The time at which customer `c` leaves the queue: its service-start time if it is served,
its deadline if it abandons. -/
noncomputable def queueExit (init : List ℝ) (a d σ : ℕ → ℝ) (c : ℕ) : ℝ :=
  (startTime init a d σ c).getD (d c)

/-- The time at which customer `c` leaves the system: the end of its service if it is served,
its deadline if it abandons. -/
noncomputable def departure (init : List ℝ) (a d σ : ℕ → ℝ) (c : ℕ) : ℝ :=
  match startTime init a d σ c with
  | some s => s + σ c
  | none => d c

/-- Structural lemma: a customer never starts service before it arrives. -/
theorem le_of_serveStep {a d σ s : ℝ} {L : List ℝ} (h : (serveStep a d σ L).1 = some s) :
    a ≤ s := by
  cases L with
  | nil => simp [serveStep] at h
  | cons v L =>
    simp only [serveStep] at h
    split_ifs at h with h1
    · simp only [Option.some.injEq] at h
      rw [← h]; exact le_max_left _ _

/-- Structural lemma: a customer never starts service before it arrives. -/
theorem arrival_le_startTime {init : List ℝ} {a d σ : ℕ → ℝ} {c : ℕ} {s : ℝ}
    (h : startTime init a d σ c = some s) : a c ≤ s :=
  le_of_serveStep h

/-- Structural lemma: a customer that is served starts service strictly before its deadline. -/
theorem lt_of_serveStep {a d σ s : ℝ} {L : List ℝ} (h : (serveStep a d σ L).1 = some s) :
    s < d := by
  cases L with
  | nil => simp [serveStep] at h
  | cons v L =>
    simp only [serveStep] at h
    split_ifs at h with h1
    · simp only [Option.some.injEq] at h
      rw [← h]; exact h1

/-- Structural lemma: a customer that is served starts service strictly before its deadline. -/
theorem startTime_lt_deadline {init : List ℝ} {a d σ : ℕ → ℝ} {c : ℕ} {s : ℝ}
    (h : startTime init a d σ c = some s) : s < d c :=
  lt_of_serveStep h

end PerfCorrMSQ


