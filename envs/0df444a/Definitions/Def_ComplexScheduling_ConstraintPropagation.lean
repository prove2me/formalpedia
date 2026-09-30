-- Prove2me | Definitions.Def_ComplexScheduling_ConstraintPropagation
-- name    : ComplexScheduling_ConstraintPropagation
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-23T20:17:58.584011+00:00
-- url     : https://prove2.me/theorems/13bd0ef4-59d2-44d6-a6e6-8d3f7354d57d
-- title:
--   Constraint propagation for the RCPSP: disjunctions, disjunctive sets, time windows, first and last activities, work
-- statement:
--   This file adds to the book's RCPSP model (mission I) the notions Section 3.6 uses for
--   **constraint propagation**. Activities are $0,\dots,n-1$ with integer processing times $p_i$
--   and integer starting times $S_i$, as in the RCPSP definition file.
--
--   **Relations between two activities** (Section 3.6.1). A **conjunction** $i\to j$ holds in a
--   schedule when $S_i+p_i\le S_j$, that is, $j$ does not start before $i$ is finished (3.109). A
--   **parallelity relation** $i\parallel j$ holds when the two activities overlap for at least one
--   time unit (3.110), and a **disjunction** $i-j$ is its negation: $i\to j$ or $j\to i$. The
--   instance carries a set $C$ of conjunctions and a set $D$ of disjunctions that every feasible
--   schedule must satisfy (initially $C_0$, the precedences, and $D_0$, the pairs that cannot share a
--   resource). A schedule *satisfies the disjunctions* $D$ when for every listed pair $i-j$ either
--   $i\to j$ or $j\to i$ holds; conjunctions are satisfied exactly when the schedule respects the
--   arcs of $C$, the notion already defined in mission II.
--
--   **Disjunctive sets** (Section 3.6.4). A set $I$ of at least two activities is **disjunctive**
--   when any two distinct members $i,j\in I$ are related by $i-j\in D$, $i\to j\in C$ or
--   $j\to i\in C$; no two of them can be processed at the same time. Its **total processing time**
--   is $P(I)=\sum_{i\in I}p_i$.
--
--   **Time windows.** Each activity $i$ has a head $r_i$ and a deadline $d_i$, and a schedule
--   respects the windows when $r_i\le S_i$ and $S_i+p_i\le d_i$ for every activity.
--
--   **First and last.** Activity $i$ **starts first** in a set $J$ when $i\in J$ and $S_i\le S_j$
--   for all $j\in J$; it **ends last** in $J$ when $i\in J$ and $S_j+p_j\le S_i+p_i$ for all
--   $j\in J$.
--
--   **Work** (Section 3.6.5). For a cumulative resource $k$ the work of activity $i$ is
--   $w_i=r_{ik}p_i$, and $W(J)=\sum_{i\in J}w_i$.
--
--   **Formalization Note** Disjunctions are unordered, so $D$ lists $i-j$ as either $(i,j)$ or
--   $(j,i)$ and the satisfaction predicate is symmetric. "Starts first" and "ends last" are read
--   with $\le$, so an activity that ties for the earliest start counts as starting first; on a
--   disjunctive set with positive processing times ties are impossible and this is the book's
--   strict reading, while for cumulative resources (Theorem 3.8) ties are possible and this is the
--   reading its proof uses. The RCPSP feasibility predicate, `FeasibleSchedule`, and the
--   arc-respecting predicate, `RespectsArcs`, are those of missions I and II and are not
--   redefined here.
-- source:
--   Peter Brucker and Sigrid Knust, Complex Scheduling, 2nd ed., Springer 2012, https://doi.org/10.1007/978-3-642-23929-8 — Section 3.6.1 "Basic relations", printed p. 162 (PDF p. 172): conjunction (3.109), parallelity (3.110) and disjunction as its negation; Section 3.6.4 "Disjunctive sets", printed pp. 168-169 (PDF pp. 178-179): disjunctive sets, P(I), time windows [r_i, d_i] and the phrases "start first" / "end last"; Section 3.6.5 "Cumulative resources", printed p. 186 (PDF p. 196): w_i = r_ik p_i and W(J).

import Mathlib

namespace ComplexScheduling

variable {n r : ℕ}

/-- A schedule satisfies the **disjunctions** `i − j` listed in `D` (as pairs `(i, j)`, the order
being immaterial) when for each of them either `i → j` or `j → i` holds, that is, the two
activities are not processed in parallel.  Brucker and Knust, *Complex Scheduling*, §3.6.1,
p. 162: a disjunction is the negation of the parallelity relation (3.110). -/
def SatisfiesDisjunctions (p : Fin n → ℕ) (D : Finset (Fin n × Fin n)) (S : Fin n → ℕ) : Prop :=
  ∀ e ∈ D, S e.1 + p e.1 ≤ S e.2 ∨ S e.2 + p e.2 ≤ S e.1

/-- A **disjunctive set** for the conjunction set `C` and the disjunction set `D`: a set `I` of at
least two activities such that any two distinct members are related by a disjunction `i − j ∈ D`
or a conjunction `i → j ∈ C` or `j → i ∈ C`.  Brucker and Knust §3.6.4, p. 168. -/
def IsDisjunctiveSet (C D : Finset (Fin n × Fin n)) (I : Finset (Fin n)) : Prop :=
  2 ≤ I.card ∧
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (i, j) ∈ D ∨ (j, i) ∈ D ∨ (i, j) ∈ C ∨ (j, i) ∈ C

/-- A schedule respects the **time windows** `[r_i, d_i]`: every activity starts no earlier than
its head `r_i` and completes no later than its deadline `d_i`.  Brucker and Knust §3.6.4,
p. 169. -/
def WithinWindows (rel dl p : Fin n → ℕ) (S : Fin n → ℕ) : Prop :=
  ∀ i, rel i ≤ S i ∧ S i + p i ≤ dl i

/-- The **total processing time** `P(J) := ∑_{i ∈ J} p_i` of a set of activities.  Brucker and
Knust §3.6.4, p. 169. -/
def totalProcessing (p : Fin n → ℕ) (J : Finset (Fin n)) : ℕ := ∑ i ∈ J, p i

/-- Activity `i` **starts first** in the set `J` under the schedule `S`: it belongs to `J` and no
activity of `J` starts earlier.  Brucker and Knust §3.6.4, p. 169. -/
def StartsFirstIn (S : Fin n → ℕ) (J : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ J ∧ ∀ j ∈ J, S i ≤ S j

/-- Activity `i` **ends last** in the set `J` under the schedule `S`: it belongs to `J` and no
activity of `J` completes later.  Brucker and Knust §3.6.4, p. 169. -/
def EndsLastIn (p S : Fin n → ℕ) (J : Finset (Fin n)) (i : Fin n) : Prop :=
  i ∈ J ∧ ∀ j ∈ J, S j + p j ≤ S i + p i

/-- The **work** `W(J) := ∑_{i ∈ J} r_{ik} p_i` that the activities of `J` need from the
cumulative resource `k`, where `w_i := r_{ik} p_i`.  Brucker and Knust §3.6.5, p. 186. -/
def totalWork (p : Fin n → ℕ) (demand : Fin n → Fin r → ℕ) (k : Fin r) (J : Finset (Fin n)) : ℕ :=
  ∑ i ∈ J, demand i k * p i

end ComplexScheduling


