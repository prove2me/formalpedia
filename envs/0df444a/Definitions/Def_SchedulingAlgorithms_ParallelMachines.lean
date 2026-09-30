-- Prove2me | Definitions.Def_SchedulingAlgorithms_ParallelMachines
-- name    : SchedulingAlgorithms_ParallelMachines
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-23T20:11:59.205435+00:00
-- url     : https://prove2.me/theorems/a4d0b0b3-9cf6-462f-9a7e-eb7c083b1fc9
-- title:
--   Preemptive schedules on parallel machines: pieces, feasibility, makespan, and the bounds (5.5) and LB
-- statement:
--   This file fixes the model of Brucker's Chapter 5 for **preemptive scheduling on parallel
--   machines**, in the generality of *uniform* machines (Section 5.1.2); identical machines are
--   the case in which every speed is $1$.
--
--   **Jobs, machines, pieces.** There are $n$ jobs with processing requirements $p_1,\dots,p_n$
--   and $m$ machines with speeds $s_1,\dots,s_m$. Executing job $i$ on machine $j$ for a period of
--   length $\ell$ performs $s_j\,\ell$ units of its requirement, so the whole job takes $p_i/s_j$
--   time units there (p. 124). Preemption is allowed: "processing may be interrupted and resumed
--   at a later time, even on another machine" (p. 3). A **preemptive schedule** is therefore a
--   finite list of **pieces**, each piece being a job, a machine, a start time and a stop time.
--
--   **Feasibility** (p. 3 and p. 124). A schedule is feasible for the data $(s,p)$ when
--
--   - every piece has $0 \le \text{start} \le \text{stop}$;
--   - no two pieces on the same machine overlap in time, and no two pieces of the same job
--     overlap in time — a machine processes one job at a time and a job is processed by one
--     machine at a time;
--   - for every job $i$, the work performed on it, $\sum s_{j(q)}\,(\text{stop}_q-\text{start}_q)$
--     over its pieces $q$, equals $p_i$.
--
--   Two pieces are *disjoint* when one stops no later than the other starts; touching intervals
--   are allowed.
--
--   **Objectives.** The **makespan** $C_{\max}$ is the largest stop time of any piece ($0$ for
--   the empty schedule). The **completion time** $C_i$ of job $i$ is the largest stop time of
--   one of its pieces, and $\sum_i w_i C_i$ is the total weighted completion time. A schedule
--   is **nonpreemptive** when every job consists of exactly one piece.
--
--   **The bounds.** Write $P_j=\sum_{i\le j}p_i$ and $S_j=\sum_{i\le j}s_i$ for the prefix sums
--   (p. 124), and, for a set $A$ of jobs, $h(A)=S_{|A|}$ if $|A|\le m$ and $h(A)=S_m$ otherwise
--   (p. 129), the largest total speed that $|A|$ jobs can use at once. The bound (5.5) of
--   p. 125 is
--
--   $$
--   w \;:=\; \max\Bigl\{\max_{j=1}^{m-1} \frac{P_j}{S_j},\ \frac{P_n}{S_m}\Bigr\},
--   $$
--
--   and the bound of p. 108 for identical machines is
--   $LB := \max\{\max_i p_i,\ (\sum_i p_i)/m\}$.
--
--   **Formalization Note** Jobs are `Fin n` and machines `Fin m`, so $p_1\ge\dots\ge p_n$ is
--   `Antitone p` and $P_j$ is the sum over the first $j$ indices. The bound $w$ is the maximum of
--   an explicit nonempty finite set, so it involves no junk value; the divisions in it are by
--   the $S_j$, which are positive whenever the speeds are, and the theorems assume that. $LB$
--   takes a proof that there is at least one job, since $\max_i p_i$ has no meaning otherwise.
--   The list model admits pieces of zero length and does not require the pieces to be sorted;
--   both are harmless, and a schedule "with a finite number of preemptions" is exactly what the
--   book manipulates in the proof of Theorem 5.7.
-- source:
--   Peter Brucker, Scheduling Algorithms, 5th ed., Springer 2007, https://doi.org/10.1007/978-3-540-69516-5 — the feasibility convention of Section 1.2, printed p. 3 (PDF p. 15), the definition of preemption in Section 1.3, printed p. 3 (PDF p. 15), the lower bound LB for P | pmtn | Cmax in Section 5.1.1, printed p. 108 (PDF p. 120), and the uniform-machine model with P_i, S_j and the bound (5.5) in Section 5.1.2, printed pp. 124-125 (PDF pp. 136-137), with h(A) on printed p. 129 (PDF p. 141).

import Mathlib

namespace SchedulingAlgorithms

noncomputable section

variable {n m : ℕ}

/-- One piece of processing in a preemptive schedule on parallel machines: job `job` is
processed on machine `machine` during the time interval from `start` to `stop`.  A preempted
job is one with several pieces, possibly on different machines.  Brucker, *Scheduling
Algorithms*, §1.3, p. 3 ("processing may be interrupted and resumed at a later time, even on
another machine"). -/
structure Piece (n m : ℕ) where
  job : Fin n
  machine : Fin m
  start : ℝ
  stop : ℝ

/-- A preemptive schedule is a finite list of pieces; a schedule "with a finite number of
preemptions" is exactly what the proof of Theorem 5.7 (p. 121) transforms. -/
abbrev PreemptiveSchedule (n m : ℕ) := List (Piece n m)

/-- Two pieces occupy disjoint time intervals. -/
def Piece.Disjoint (a b : Piece n m) : Prop := a.stop ≤ b.start ∨ b.stop ≤ a.start

/-- The amount of work of job `i` done by the schedule on uniform machines with speeds `s`:
a piece of length `stop - start` on machine `j` performs `s j * (stop - start)` units of the
job's processing requirement.  Brucker §5.1.2, p. 124 ("Execution of job `J_i` on machine
`M_j` requires `p_i / s_j` time units"). -/
def work (s : Fin m → ℝ) (S : PreemptiveSchedule n m) (i : Fin n) : ℝ :=
  ((S.filter fun q => q.job = i).map fun q => s q.machine * (q.stop - q.start)).sum

/-- A feasible preemptive schedule for processing requirements `p` on uniform machines with
speeds `s`: every piece lies in `[0, ∞)`, no two pieces on the same machine overlap, no two
pieces of the same job overlap (a job is processed by at most one machine at a time), and
every job receives exactly its processing requirement.  Brucker §1.2, p. 3 ("A schedule is
feasible if no two time intervals overlap on the same machine, if no two time intervals
allocated to the same job overlap") and §5.1.2, p. 124. -/
def IsFeasible (s : Fin m → ℝ) (p : Fin n → ℝ) (S : PreemptiveSchedule n m) : Prop :=
  (∀ q ∈ S, 0 ≤ q.start ∧ q.start ≤ q.stop) ∧
    S.Pairwise (fun a b => (a.machine = b.machine ∨ a.job = b.job) → Piece.Disjoint a b) ∧
    ∀ i, work s S i = p i

/-- The makespan `C_max`: the latest finishing time of any piece, `0` for the empty schedule. -/
def makespan (S : PreemptiveSchedule n m) : ℝ :=
  (S.map Piece.stop).foldr max 0

/-- The completion time `C_i` of job `i`: the latest finishing time of one of its pieces. -/
def completion (S : PreemptiveSchedule n m) (i : Fin n) : ℝ :=
  ((S.filter fun q => q.job = i).map Piece.stop).foldr max 0

/-- The total weighted completion time `∑ w_i C_i`. -/
def totalWeightedCompletionOf (w : Fin n → ℝ) (S : PreemptiveSchedule n m) : ℝ :=
  ∑ i, w i * completion S i

/-- A schedule without preemption: every job is processed in one uninterrupted piece on one
machine.  Brucker §1.3, p. 3. -/
def Nonpreemptive (S : PreemptiveSchedule n m) : Prop :=
  ∀ i, (S.filter fun q => q.job = i).length = 1

/-- The prefix sum `∑_{i=1}^{j} f_i` of a finite sequence, for `j = 0, 1, …` (indices of `Fin k`
being `0`-based, this is the sum over the first `j` entries; for `j ≥ k` it is the total).
Brucker §5.1.2, p. 124: `P_i = p_1 + … + p_i` and `S_j = s_1 + … + s_j`. -/
def prefixSum {k : ℕ} (f : Fin k → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < j), f i

/-- The bound (5.5) of Brucker §5.1.2, p. 125, for `Q | pmtn | C_max`:
`w := max { max_{j=1}^{m-1} P_j / S_j , P_n / S_m }`, with `P_j` the sum of the `j` largest
processing requirements and `S_j` the sum of the `j` largest speeds.  Stated for the sorted
data `p_1 ≥ … ≥ p_n` and `s_1 ≥ … ≥ s_m` with `n ≥ m`, as on that page. -/
def levelBound (s : Fin m → ℝ) (p : Fin n → ℝ) : ℝ :=
  (insert (prefixSum p n / prefixSum s m)
      ((Finset.Ico 1 m).image fun j => prefixSum p j / prefixSum s j)).max'
    (Finset.insert_nonempty _ _)

/-- The sum of the `min(|A|, m)` largest speeds: Brucker's `h(A) = S_{|A|}` if `|A| ≤ m` and
`S_m` otherwise, §5.1.2, p. 129. -/
def speedCapacity (s : Fin m → ℝ) (A : Finset (Fin n)) : ℝ :=
  prefixSum s (min A.card m)

/-- The bound `LB := max { max_i p_i , (∑_i p_i) / m }` of Brucker §5.1.1, p. 108, for
`P | pmtn | C_max` on `m` identical machines; needs at least one job for the inner maximum. -/
def mcNaughtonBound (hn : 0 < n) (p : Fin n → ℝ) (m : ℕ) : ℝ :=
  max (Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ p) ((∑ i, p i) / m)

end

end SchedulingAlgorithms


