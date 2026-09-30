-- Prove2me | Definitions.Def_ComplexScheduling_RCPSP
-- name    : ComplexScheduling_RCPSP
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-18T15:59:45.119849+00:00
-- url     : https://prove2.me/theorems/2f68bb97-b2e2-4613-befc-84e524703df9
-- title:
--   The resource-constrained project scheduling problem and its schedule classes
-- statement:
--   This file fixes the **resource-constrained project scheduling problem** (RCPSP), the central
--   model of Brucker and Knust's book, together with the left-shift classification of its schedules.
--
--   **The problem.** There are $n$ activities and $r$ renewable resources. Activity $i$ must be
--   processed without interruption for $p_i$ time units, during which it occupies a constant
--   $r_{ik}$ units of resource $k$; a constant $R_k$ units of resource $k$ is available at every
--   time. Precedence constraints are given as a set of pairs $i\to j$, meaning $j$ cannot start
--   before $i$ is complete. All data are integers.
--
--   A **schedule** assigns each activity an integer starting time $S_i$, and its completion times are
--   $C_i=S_i+p_i$. It is **feasible** when
--
--   1. every precedence constraint holds, $S_i+p_i\le S_j$ whenever $i\to j$; and
--   2. at every time $t$ the total demand does not exceed the capacity,
--      $\displaystyle\sum_{i\,:\,S_i\le t<S_i+p_i} r_{ik}\;\le\;R_k$ for every resource $k$.
--
--   **Left shifts.** A **left shift** of activity $i$ moves it to an earlier start, leaving every
--   other activity where it is, and lands on a feasible schedule. It is a **local** left shift when
--   it can be reached by successive one-period shifts — every intermediate schedule being feasible —
--   and a **global** left shift otherwise, meaning some intermediate schedule violates a resource
--   constraint. A feasible schedule is **semi-active** when no local left shift is possible for any
--   activity, and **active** when no left shift at all, local or global, is possible.
--
--   **Objectives.** An objective $f$ evaluated on the completion-time vector is **regular** when it is
--   monotone nondecreasing: $f(C)\le f(C')$ whenever $C_i\le C'_i$ for every $i$. Makespan, total
--   weighted completion time, maximum lateness and the weighted number of late activities are all
--   regular. A schedule is **optimal** when no feasible schedule gives a smaller value of $f$.
--
--   **Formalization Note** Starting times are natural numbers, matching the book's "all data are
--   assumed to be integers" and $S_i\in\{0,1,\dots,T\}$; no finite horizon $T$ is imposed, which only
--   enlarges the feasible set. Precedence constraints are a `Finset` of pairs rather than a relation,
--   so they are finite and decidable, and no acyclicity is assumed — an inconsistent set simply has
--   no feasible schedule. The resource constraint is quantified over every natural time $t$, which is
--   equivalent to quantifying over $t\le T$ because no activity is in process beyond the last
--   completion. `Active` is stated as "no left shift", which is the book's "no local or global left
--   shift" unfolded: a global left shift is by definition one that is not local, so the two cases are
--   exhaustive.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 1.1 "The RCPSP and some Generalizations", printed pp. 1-2 (PDF pp. 12-13) for the problem; Section 1.2, printed p. 18, for regular objective functions; Section 3.1.2 "A classification of schedules", printed pp. 119-120 (PDF pp. 129-130) for left shifts and the semi-active / active classification.

import Mathlib

namespace ComplexScheduling

variable {n r : ℕ}

/-- Activity `i` is in process at the integer time `t` under the schedule `S`: it has started
and has not yet completed.  Brucker and Knust, *Complex Scheduling*, §1.1, p. 1. -/
def InProcess (p : Fin n → ℕ) (S : Fin n → ℕ) (t : ℕ) (i : Fin n) : Prop :=
  S i ≤ t ∧ t < S i + p i

instance (p : Fin n → ℕ) (S : Fin n → ℕ) (t : ℕ) : DecidablePred (InProcess p S t) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The total amount of resource `k` occupied at time `t`: activity `i` occupies `demand i k`
units throughout its processing.  Brucker and Knust §1.1, p. 1. -/
def resourceUsage (p : Fin n → ℕ) (demand : Fin n → Fin r → ℕ) (S : Fin n → ℕ)
    (k : Fin r) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (InProcess p S t), demand i k

/-- A schedule assigns each activity an integer starting time; it is **feasible** when the
precedence constraints `i → j`, given as pairs in `prec`, are met — `S i + p i ≤ S j` — and when
at every time the demand for each resource is within its capacity.  Brucker and Knust §1.1,
pp. 1-2. -/
def FeasibleSchedule (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) : Prop :=
  (∀ e ∈ prec, S e.1 + p e.1 ≤ S e.2) ∧
    ∀ (k : Fin r) (t : ℕ), resourceUsage p demand S k t ≤ Rcap k

/-- The schedule obtained from `S` by starting activity `i` at time `s` instead, every other
activity left where it was. -/
def restart (S : Fin n → ℕ) (i : Fin n) (s : ℕ) : Fin n → ℕ := Function.update S i s

/-- A **left shift** of activity `i` to time `s`: `s < S i` and the result is feasible, all other
activities unmoved.  Brucker and Knust §3.1.2, p. 119. -/
def LeftShiftTo (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) (i : Fin n) (s : ℕ) : Prop :=
  s < S i ∧ FeasibleSchedule p Rcap demand prec (restart S i s)

/-- A **local left shift**: a left shift reachable by successive one-period left shifts, so every
intermediate schedule — the start of `i` lowered one time unit at a time — is itself feasible.
Brucker and Knust §3.1.2, pp. 119-120. -/
def LocalLeftShiftTo (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) (i : Fin n) (s : ℕ) : Prop :=
  s < S i ∧ ∀ u : ℕ, s ≤ u → u ≤ S i → FeasibleSchedule p Rcap demand prec (restart S i u)

/-- A feasible schedule is **semi-active** when no local left shift is possible for any activity.
Brucker and Knust §3.1.2, p. 120. -/
def SemiActive (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) : Prop :=
  FeasibleSchedule p Rcap demand prec S ∧
    ∀ (i : Fin n) (s : ℕ), ¬ LocalLeftShiftTo p Rcap demand prec S i s

/-- A feasible schedule is **active** when no left shift at all — local or global — is possible
for any activity.  Brucker and Knust §3.1.2, p. 120. -/
def Active (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (S : Fin n → ℕ) : Prop :=
  FeasibleSchedule p Rcap demand prec S ∧
    ∀ (i : Fin n) (s : ℕ), ¬ LeftShiftTo p Rcap demand prec S i s

/-- The completion times `C i = S i + p i` of a schedule.  Brucker and Knust §1.1, p. 2. -/
def completion (p : Fin n → ℕ) (S : Fin n → ℕ) : Fin n → ℕ := fun i => S i + p i

/-- An objective is **regular** when it is monotone nondecreasing in the completion times:
`f C ≤ f C'` whenever `C i ≤ C' i` for every activity.  Brucker and Knust §1.2, p. 18. -/
def Regular (f : (Fin n → ℕ) → ℝ) : Prop :=
  ∀ C C' : Fin n → ℕ, (∀ i, C i ≤ C' i) → f C ≤ f C'

/-- The objective value of a schedule: `f` evaluated at its completion-time vector. -/
def scheduleValue (p : Fin n → ℕ) (f : (Fin n → ℕ) → ℝ) (S : Fin n → ℕ) : ℝ :=
  f (completion p S)

/-- `S` is optimal when no feasible schedule has a smaller objective value. -/
def IsOptimalSchedule (p : Fin n → ℕ) (Rcap : Fin r → ℕ) (demand : Fin n → Fin r → ℕ)
    (prec : Finset (Fin n × Fin n)) (f : (Fin n → ℕ) → ℝ) (S : Fin n → ℕ) : Prop :=
  FeasibleSchedule p Rcap demand prec S ∧
    ∀ S' : Fin n → ℕ, FeasibleSchedule p Rcap demand prec S' →
      scheduleValue p f S ≤ scheduleValue p f S'

end ComplexScheduling


