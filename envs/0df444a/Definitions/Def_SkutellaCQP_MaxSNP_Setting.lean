-- Prove2me | Definitions.Def_SkutellaCQP_MaxSNP_Setting
-- name    : SkutellaCQP_MaxSNP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:48.414464+00:00
-- url     : https://prove2.me/theorems/1d225218-63fa-4f59-a994-0560dd757971
-- title:
--   §7, p. 32 — 3-Occurrence Max3Sat instances, the scheduling instance R(I) of R | rⱼ | Σ Cⱼ, schedules, VAL(S) and SAT(S)
-- statement:
--   This file fixes the objects of §7 of Skutella's paper: instances of 3-OCCURRENCE MAX3SAT and the scheduling instance $R(I)$ of $R\,|\,r_j\,|\sum C_j$ built from them.
--
--   **The satisfiability problem.** An instance $I$ has $n$ variables $x$ and $m$ clauses $c$. A literal is a variable $x$ or its negation $\neg x$, and each clause is a set of literals. $I$ is an instance of 3-OCCURRENCE MAX3SAT when
--
--   1. every clause contains at least one and at most three literals;
--   2. every variable occurs at most three times in the clauses, occurrences of $x$ and of $\neg x$ counted together;
--   3. every variable occurs at least once.
--
--   A truth assignment $t$ gives each variable the value true or false. It satisfies a clause when some literal of the clause is true under $t$. $\#(t)$ is the number of clauses that $t$ satisfies, and $\mathrm{OPT}_{\mathrm{SAT}}(I)=\max_t\#(t)$.
--
--   **The scheduling instance $R(I)$** (p. 32). There are $n+m$ jobs and $2n$ machines.
--
--   1. For each variable $x$ there is a *true machine* and a *false machine*, and one *v-job*, released at time $0$, with processing time $4$ on the two machines of $x$. It cannot be processed on any other machine (processing time infinity).
--   2. For each clause $c$ there is one *c-job*, released at time $3$, with processing time $0$. It can be processed on the false machine of $x$ if $x$ occurs nonnegated in $c$, and on the true machine of $x$ if $\neg x$ occurs in $c$, and on no other machine.
--
--   A schedule $S$ assigns every job $j$ a machine and a start time $S_j$. It is *feasible* when every job runs on a machine where it may be processed, $S_j\ge r_j$, and two distinct jobs $j,k$ on the same machine satisfy $S_j+p_j\le S_k$ or $S_k+p_k\le S_j$. Its value is the total completion time
--   $$
--   \mathrm{VAL}(S)=\sum_j C_j=\sum_j (S_j+p_j).
--   $$
--   The truth assignment $\mathrm{SAT}(S)$ sets $x$ true if and only if the v-job of $x$ is processed on the true machine of $x$.
--
--   These objects are shared by every statement of the mission. The construction is the reduction by which the paper reproves the MaxSNP-hardness of $R\,|\,r_j\,|\sum C_j$.
--
--   **Formalization Note** Variables and clauses are `Fin n` and `Fin m` (here $n$ and $m$ count variables and clauses, not jobs and machines as elsewhere in the paper). A literal is a pair `(x, b)`: `(x, true)` is $x$ and `(x, false)` is $\neg x$. A clause is a `Finset` of literals, so it cannot repeat a literal but may contain both $x$ and $\neg x$. Jobs are `Fin n ⊕ Fin m` (v-jobs, then c-jobs), and machines are `Fin n × Bool`, with `(x, true)` the true machine. Infinite processing times are encoded by the eligibility relation `Eligible`. The non-overlap condition, rather than disjointness of half-open intervals $[S_j,S_j+p_j)$, decides when a job of length $0$ conflicts: a c-job started at time $3$ conflicts with a v-job processed over $[0,4)$ on the same machine ($4\le3$ and $3\le0$ both fail), but several c-jobs may start at the same time on one machine. This is the paper's reading ("a c-job can be started at time 3 without getting in conflict with a v-job if and only if the clause is satisfied", p. 32). Conditions 1 and 3 of 3-OCCURRENCE MAX3SAT are not written on the page. Condition 1 is part of MAX3SAT: an empty clause would leave its c-job without a machine. Condition 3 is used by the proof of Theorem 7.2 ($n\le3m$).
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 32, §7 (definition of 3-OCCURRENCE MAX3SAT and construction of R(I)); p. 33 (OPT_SCH, OPT_SAT)

import Mathlib

namespace SkutellaCQP.MaxSNP

open Finset

/-- An instance of 3-OCCURRENCE MAX3SAT with `n` variables and `m` clauses (§7, p. 32). Clause `c`
is a finite set of literals; the literal `(x, true)` is the variable `x`, and `(x, false)` is its
negation `¬x`. The side conditions of the problem are in `Occ3Max3Sat.IsValid`. -/
structure Occ3Max3Sat (n m : ℕ) where
  clause : Fin m → Finset (Fin n × Bool)

variable {n m : ℕ}

/-- The instance is one of 3-OCCURRENCE MAX3SAT: every clause has between one and three literals,
every variable occurs (as `x` or as `¬x`, counted together over all clauses) at most three times,
and every variable occurs at least once. -/
def Occ3Max3Sat.IsValid (I : Occ3Max3Sat n m) : Prop :=
  (∀ c, 1 ≤ (I.clause c).card ∧ (I.clause c).card ≤ 3) ∧
  (∀ x, (∑ c, ((I.clause c).filter (fun ℓ => ℓ.1 = x)).card) ≤ 3) ∧
  (∀ x, ∃ c b, (x, b) ∈ I.clause c)

/-- The truth assignment `t` satisfies the clause `C`: some literal `(x, b)` of `C` has `t x = b`. -/
def Satisfies (t : Fin n → Bool) (C : Finset (Fin n × Bool)) : Prop :=
  ∃ ℓ ∈ C, t ℓ.1 = ℓ.2

instance (t : Fin n → Bool) (C : Finset (Fin n × Bool)) : Decidable (Satisfies t C) := by
  unfold Satisfies; infer_instance

/-- `#(t)`: the number of clauses of `I` satisfied by the truth assignment `t`. -/
def satCount (I : Occ3Max3Sat n m) (t : Fin n → Bool) : ℕ :=
  (univ.filter fun c => Satisfies t (I.clause c)).card

/-- `OPT_SAT(I)`: the largest number of clauses satisfied by a truth assignment. -/
def optSat (I : Occ3Max3Sat n m) : ℕ :=
  univ.sup (satCount I)

/-- Jobs of `R(I)`: one v-job `inl x` per variable and one c-job `inr c` per clause (`n + m` jobs). -/
abbrev Job (n m : ℕ) := Fin n ⊕ Fin m

/-- Machines of `R(I)`: `(x, true)` is the true machine and `(x, false)` the false machine of the
variable `x` (`2n` machines). -/
abbrev Machine (n : ℕ) := Fin n × Bool

/-- The machines on which a job may be processed (processing time finite). A v-job may run only on
the two machines of its variable. A c-job may run on the false machine of `x` iff `x` occurs
nonnegated in its clause, and on the true machine of `x` iff `¬x` occurs in its clause. -/
def Eligible (I : Occ3Max3Sat n m) : Job n m → Machine n → Prop
  | Sum.inl x, y => y.1 = x
  | Sum.inr c, y => (y.1, !y.2) ∈ I.clause c

/-- Processing times of `R(I)`: 4 for a v-job, 0 for a c-job (on every eligible machine). -/
def ptime : Job n m → ℝ
  | Sum.inl _ => 4
  | Sum.inr _ => 0

/-- Release dates of `R(I)`: 0 for a v-job, 3 for a c-job. -/
def rel : Job n m → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 3

/-- A nonpreemptive schedule: a machine and a start time for every job. -/
structure Sched (n m : ℕ) where
  mach : Job n m → Machine n
  start : Job n m → ℝ

/-- Feasibility for `R(I)`: every job runs on an eligible machine, no job starts before its release
date, and two distinct jobs on the same machine do not overlap, in the sense that one of them
completes no later than the other starts. Under this condition a job of length 0 started at time
`s` conflicts with a job processed over `[a, a + p)` with `a < s < a + p`. -/
def Feasible (I : Occ3Max3Sat n m) (S : Sched n m) : Prop :=
  (∀ j, Eligible I j (S.mach j)) ∧
  (∀ j, rel j ≤ S.start j) ∧
  (∀ j k, j ≠ k → S.mach j = S.mach k →
    S.start j + ptime j ≤ S.start k ∨ S.start k + ptime k ≤ S.start j)

/-- `VAL(S)`: the total completion time `∑_j C_j` of the schedule, with `C_j = S_j + p_j`. -/
def VAL (S : Sched n m) : ℝ :=
  ∑ j, (S.start j + ptime j)

/-- `SAT(S)`: the variable `x` is set to true iff its v-job is processed on its true machine. -/
def SAT (S : Sched n m) : Fin n → Bool :=
  fun x => (S.mach (Sum.inl x)).2

end SkutellaCQP.MaxSNP


