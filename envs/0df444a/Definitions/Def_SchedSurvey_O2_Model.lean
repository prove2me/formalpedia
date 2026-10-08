-- Prove2me | Definitions.Def_SchedSurvey_O2_Model
-- name    : SchedSurvey_O2_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:29:40.011935+00:00
-- url     : https://prove2.me/theorems/31a08556-914c-428e-bce4-3561ddf19f4b
-- title:
--   §2.1, §2.3, §2.4, §5.2.1, pp. 288–289, 311 — two-machine open-shop schedules, feasibility, completion by T, T₁, T₂, A, B
-- statement:
--   This file sets up the two-machine open shop $O2$ of Graham, Lawler, Lenstra and Rinnooy Kan (1979).
--
--   There are $n$ jobs $J_1,\dots,J_n$ and two machines $M_1, M_2$. Job $J_j$ consists of two operations: $O_{1j}$, which must be processed on $M_1$ for $a_j = p_{1j}$ time units, and $O_{2j}$, which must be processed on $M_2$ for $b_j = p_{2j}$ time units; the order in which the two operations of a job are executed is immaterial (open shop). Preemption is not allowed, so a **schedule** $S$ is given by the start times $s_1(j)$ of $O_{1j}$ and $s_2(j)$ of $O_{2j}$; the operations occupy the time intervals $[s_1(j), s_1(j)+a_j)$ and $[s_2(j), s_2(j)+b_j)$.
--
--   Two intervals $[s, s+p)$ and $[s', s'+p')$ **do not overlap** if $s + p \le s'$ or $s' + p' \le s$. A schedule is **feasible on a job set** $J$ if, for the jobs of $J$:
--
--   1. no operation starts before time $0$ (all jobs are available at time $0$);
--   2. machine $M_1$ processes at most one job at a time: the $M_1$-intervals of two distinct jobs do not overlap;
--   3. machine $M_2$ processes at most one job at a time;
--   4. each job is processed on at most one machine at a time: the $M_1$-interval and the $M_2$-interval of the same job do not overlap (in either order).
--
--   A schedule is **feasible** if it is feasible on the set of all jobs. It **completes by** $T$ if every operation ends by $T$:
--   $$
--   s_1(j) + a_j \le T \quad\text{and}\quad s_2(j) + b_j \le T \qquad \text{for all } j,
--   $$
--   that is, $C_{\max} \le T$. The file also defines the machine loads $T_1 = \sum_j a_j$ and $T_2 = \sum_j b_j$, the job sets
--   $$
--   A = \{J_j \mid a_j \ge b_j\}, \qquad B = \{J_j \mid a_j < b_j\},
--   $$
--   and, for a list $\sigma$ of jobs and processing times $p$, the start offset $\mathrm{contigStart}_p(\sigma, j)$: the total processing time of the jobs listed before $j$ in $\sigma$, i.e. the start time of $j$ when the jobs of $\sigma$ run back to back, in that order, from time $0$.
--
--   These are the objects of the analysis of $O2\|C_{\max}$ in §5.2.1 of the survey.
--
--   **Formalization Note** Jobs are `Fin n`, 0-based: $J_j$ is index $j-1$. Processing and start times are real numbers (the survey's integer data are a special case). The standing assumptions of §2.1 (each machine processes at most one job at a time, each job is on at most one machine at a time) are clauses 2–4 of feasibility; §2.4 (4) ($r_j = 0$) gives clause 1. Touching intervals are allowed, so an operation of length $0$ occupies nothing.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 288, §2.1; pp. 288–289, §2.3; p. 289, §2.4 (1), (4); p. 290, §2.5; p. 311, §5.2.1

import Mathlib

namespace SchedSurvey.O2

/-- A nonpreemptive two-machine open-shop schedule of the jobs `Fin n` (job `Jⱼ` of the paper is
index `j - 1`): `s₁ j` is the start time of the operation `O₁ⱼ` on machine `M₁`, and `s₂ j` the
start time of `O₂ⱼ` on machine `M₂`. Without preemption a schedule is exactly its start times. -/
structure Schedule (n : ℕ) where
  /-- start time of job `j` on machine `M₁` -/
  s₁ : Fin n → ℝ
  /-- start time of job `j` on machine `M₂` -/
  s₂ : Fin n → ℝ

/-- The half-open time intervals `[s, s + p)` and `[s', s' + p')` do not overlap: one ends no later
than the other starts (touching intervals are allowed). -/
def NoOverlap (s p s' p' : ℝ) : Prop :=
  s + p ≤ s' ∨ s' + p' ≤ s

/-- Feasibility of a schedule `S` restricted to the job set `J`, for processing times `a j = p₁ⱼ`
on `M₁` and `b j = p₂ⱼ` on `M₂` (Graham et al. 1979, §2.1, §2.3, §2.4(4)):
* no operation of a job of `J` starts before time `0` (all release dates are `0`);
* `M₁` processes at most one job of `J` at a time;
* `M₂` processes at most one job of `J` at a time;
* each job of `J` is processed on at most one machine at a time, its two operations being
  executed in either order (open shop). -/
def IsFeasibleOn {n : ℕ} (J : Finset (Fin n)) (a b : Fin n → ℝ) (S : Schedule n) : Prop :=
  (∀ j ∈ J, 0 ≤ S.s₁ j ∧ 0 ≤ S.s₂ j) ∧
  (∀ j ∈ J, ∀ k ∈ J, j ≠ k → NoOverlap (S.s₁ j) (a j) (S.s₁ k) (a k)) ∧
  (∀ j ∈ J, ∀ k ∈ J, j ≠ k → NoOverlap (S.s₂ j) (b j) (S.s₂ k) (b k)) ∧
  (∀ j ∈ J, NoOverlap (S.s₁ j) (a j) (S.s₂ j) (b j))

/-- A feasible schedule of all `n` jobs for the open shop `O2` with processing times `a`, `b`. -/
def IsFeasible {n : ℕ} (a b : Fin n → ℝ) (S : Schedule n) : Prop :=
  IsFeasibleOn Finset.univ a b S

/-- Every operation of `S` is completed by time `T`, i.e. `Cmax ≤ T`. -/
def CompletesBy {n : ℕ} (a b : Fin n → ℝ) (S : Schedule n) (T : ℝ) : Prop :=
  ∀ j, S.s₁ j + a j ≤ T ∧ S.s₂ j + b j ≤ T

/-- `T₁ = Σⱼ aⱼ`, the total processing time on `M₁`. -/
def T₁ {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  ∑ j, a j

/-- `T₂ = Σⱼ bⱼ`, the total processing time on `M₂`. -/
def T₂ {n : ℕ} (b : Fin n → ℝ) : ℝ :=
  ∑ j, b j

/-- `A = {Jⱼ | aⱼ ≥ bⱼ}` (§5.2.1, p. 311). -/
noncomputable def setA {n : ℕ} (a b : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => b j ≤ a j)

/-- `B = {Jⱼ | aⱼ < bⱼ}` (§5.2.1, p. 311). -/
noncomputable def setB {n : ℕ} (a b : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => a j < b j)

/-- Start offset of job `j` when the jobs of the list `σ` are processed back to back, in the order
of `σ`, from time `0` on one machine with processing times `p`: the total processing time of the
jobs preceding the first occurrence of `j` in `σ`. (For `j ∉ σ` it is the total of `σ`.) -/
def contigStart {n : ℕ} (p : Fin n → ℝ) (σ : List (Fin n)) (j : Fin n) : ℝ :=
  ((σ.takeWhile (fun k => decide (k ≠ j))).map p).sum

end SchedSurvey.O2


