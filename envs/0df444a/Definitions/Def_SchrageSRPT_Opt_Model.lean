-- Prove2me | Definitions.Def_SchrageSRPT_Opt_Model
-- name    : SchrageSRPT_Opt_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:25.690028+00:00
-- url     : https://prove2.me/theorems/c20e2b0b-71d3-4366-bdb6-b1295c778487
-- title:
--   DEFINITIONS and ASSUMPTIONS, pp. 687–688 — schedules δ(n, t), S(n, t), C(n), θ(t), N(t), the SRPT discipline, and the revised schedules of PROOF
-- statement:
--   This item sets up the single-server model of L. Schrage's letter on the Shortest Remaining Processing Time (SRPT) discipline.
--
--   **Arrival stream.** An arrival stream is a sequence of pairs $\{A(n), P(n)\}$, $n = 0, 1, 2, \dots$, where $A(n) \in \mathbb R$ is the arrival time and $P(n) \in \mathbb R$ the processing time of job $n$.
--
--   **Schedule.** A schedule is a family of functions $\delta(n, \cdot) : \mathbb R \to \mathbb R$ such that
--
--   1. $\delta(n, t) \in \{0, 1\}$ for all $n, t$, where $\delta(n, t) = 1$ means that the processor is devoted to job $n$ at time $t$;
--   2. each $\delta(n, \cdot)$ is Lebesgue measurable;
--   3. $\delta(n, t) = 0$ for $t < A(n)$: no job is processed before it arrives;
--   4. the processor is devoted to at most one job at a time: $\delta(n, t) = \delta(m, t) = 1$ implies $n = m$ (the letter's constraint $\sum_n \delta(n, t) \le 1$).
--
--   **Remaining processing time and completion time.** The remaining processing time of job $n$ at time $t$ is
--   $$S(n, t) = P(n) - \int_{A(n)}^{t} \delta(n, x)\, dx,$$
--   and the completion time of job $n$ is
--   $$C(n) = \min\Big\{x \ge A(n) : \int_{A(n)}^{x} \delta(n, t)\, dt \ge P(n)\Big\},$$
--   taken to be $+\infty$ when no such $x$ exists (the job never receives its processing time).
--
--   **Jobs in system.** The set of jobs in system at time $t$ is $\theta(t) = \{n : A(n) \le t,\ S(n, t) > 0\}$, and $N(t)$ is its cardinality: a job is in system from its arrival until its completion.
--
--   **SRPT.** A schedule follows the SRPT discipline if it is a schedule and, at every time $t$ at which $\theta(t)$ is nonempty, the processor is devoted to a job $k \in \theta(t)$ with $S(k, t) \le S(j, t)$ for every $j \in \theta(t)$: "the processor should at all times process that job of those available, which has the shortest remaining processing time". Ties may be broken arbitrarily.
--
--   **Revised schedules of the proof.** Given an original schedule $\delta_o$:
--
--   1. the *idle fill* of job $j$ over $[t, t+v]$ processes $j$ throughout $[t, t+v]$, no other job there, and agrees with $\delta_o$ outside $[t, t+v]$;
--   2. the *SRPT reassignment* of jobs $j, k$ after time $t$ agrees with $\delta_o$ before $t$ and on every other job; from time $t$ on, the capacity $c(x) = \delta_o(j, x) + \delta_o(k, x)$ that $\delta_o$ gives to the pair is given to $j$ as long as $\int_t^x c(y)\, dy < S_o(j, t)$, and to $k$ afterwards.
--
--   These objects are used by every theorem of the mission: the goal compares $N(t)$ under an SRPT schedule with $N(t)$ under any schedule of the same stream, and the milestones follow the interchange argument of the letter's PROOF.
--
--   **Formalization Note.** Jobs are indexed by $\mathbb N$ from $0$ (the letter starts at $1$). Assumption (I) of the letter (the arrival stream does not depend on the discipline) is encoded by comparing two schedules of one fixed stream $(A, P)$; Assumption (II) (preemption wastes no processing) is encoded by the formula for $S(n, t)$, which has no setup term. Measurability of $\delta(n, \cdot)$ is added so that the integrals are meaningful. $C(n)$ takes values in $\mathbb R \cup \{+\infty\}$ (`WithTop ℝ`); the infimum is a minimum whenever the set is nonempty, because it is closed and bounded below. $N(t)$ is `Set.ncard`, which is the true count when finitely many jobs have arrived by time $t$; the theorems that use it assume this local finiteness. The displayed condition of p. 688 ("$S(k,t) > S(j,t)$ for $j \in \theta(t)$ implies $\delta(k,t) = 0$") is implied by the SRPT predicate but is not used to define it, since the schedule that never processes anything satisfies it.
-- source:
--   Schrage, A proof of the optimality of the shortest remaining processing time discipline, Oper. Res. 16 (1968), pp. 687–688, introduction (SRPT rule), DEFINITIONS and ASSUMPTIONS; p. 689, PROOF (case (b1) revision, reassignment over σ). DOI 10.1287/opre.16.3.687

import Mathlib

namespace SchrageSRPT.Opt

open MeasureTheory

/-- A **schedule** of the arrival stream with arrival times `A` (Schrage 1968, DEFINITIONS,
p. 688): `δ n t ∈ {0, 1}` says whether the processor is devoted to job `n` at time `t`;
each `δ n` is measurable; no job is processed before it arrives (`δ n t = 0` for `t < A n`);
and the processor is devoted to at most one job at a time (the page's `Σ_n δ(n, t) ≤ 1`). -/
def IsSchedule (A : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n t, δ n t = 0 ∨ δ n t = 1) ∧
  (∀ n, Measurable (δ n)) ∧
  (∀ n t, t < A n → δ n t = 0) ∧
  (∀ t n m, δ n t = 1 → δ m t = 1 → n = m)

/-- The processing time remaining for job `n` at time `t`,
`S(n, t) = P(n) - ∫_{A(n)}^{t} δ(n, x) dx` (p. 688). -/
noncomputable def remaining (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  P n - ∫ x in (A n)..t, δ n x

/-- The set of times `x ≥ A(n)` by which job `n` has received its processing time,
`{x : ∫_{A(n)}^{x} δ(n, t) dt ≥ P(n)}` (p. 688). -/
def completedBy (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (n : ℕ) : Set ℝ :=
  {x | A n ≤ x ∧ P n ≤ ∫ t in (A n)..x, δ n t}

open Classical in
/-- The completion time `C(n) = min {x : ∫_{A(n)}^{x} δ(n, t) dt ≥ P(n)}` (p. 688), with value
`⊤` when job `n` never receives its processing time. -/
noncomputable def completion (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (n : ℕ) : WithTop ℝ :=
  if (completedBy A P δ n).Nonempty then ((sInf (completedBy A P δ n) : ℝ) : WithTop ℝ) else ⊤

/-- The set `θ(t)` of jobs in system at time `t` (p. 688): the jobs that have arrived and still
have positive remaining processing time. -/
def inSystem (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (t : ℝ) : Set ℕ :=
  {n | A n ≤ t ∧ 0 < remaining A P δ n t}

/-- The number `N(t)` of jobs in system at time `t` (p. 688). It is a genuine count when only
finitely many jobs have arrived by time `t`. -/
noncomputable def numInSystem (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) (t : ℝ) : ℕ :=
  (inSystem A P δ t).ncard

/-- The **SRPT discipline** (p. 687): "the processor should at all times process that job of
those available, which has the shortest remaining processing time". At every time `t` at which
some job is in system, the processor serves a job in system whose remaining processing time is
smallest among the jobs in system (ties broken arbitrarily). -/
def IsSRPT (A P : ℕ → ℝ) (δ : ℕ → ℝ → ℝ) : Prop :=
  IsSchedule A δ ∧
  ∀ t, (inSystem A P δ t).Nonempty →
    ∃ k ∈ inSystem A P δ t, δ k t = 1 ∧
      ∀ j ∈ inSystem A P δ t, remaining A P δ k t ≤ remaining A P δ j t

/-- The revised schedule of case (b1) of PROOF (p. 689): job `j` is processed throughout
`[t, t + v]` ("setting `δ_r(j, x) = 1` for `t ≤ x ≤ t + v`"), every other job is switched off
there, and the original schedule `δo` is kept outside `[t, t + v]`. -/
noncomputable def idleFill (δo : ℕ → ℝ → ℝ) (j : ℕ) (t v : ℝ) : ℕ → ℝ → ℝ :=
  fun n x => if t ≤ x ∧ x ≤ t + v then (if n = j then 1 else 0) else δo n x

/-- The revised schedule of case (b2) of PROOF (p. 689): from time `t` on, the processing
capacity `δo(j, x) + δo(k, x)` that the original schedule `δo` devotes to the pair `{j, k}` is
reassigned to them according to SRPT with `j` first: `j` receives all of it until it has received
its remaining time `S_o(j, t)`, and `k` receives it afterwards. Before `t`, and for every other
job, `δo` is unchanged. -/
noncomputable def srptReassign (A P : ℕ → ℝ) (δo : ℕ → ℝ → ℝ) (j k : ℕ) (t : ℝ) :
    ℕ → ℝ → ℝ :=
  fun n x =>
    if x < t then δo n x
    else if n = j then
      (if (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t then δo j x + δo k x else 0)
    else if n = k then
      (δo j x + δo k x) -
        (if (∫ y in t..x, (δo j y + δo k y)) < remaining A P δo j t then δo j x + δo k x else 0)
    else δo n x

end SchrageSRPT.Opt


