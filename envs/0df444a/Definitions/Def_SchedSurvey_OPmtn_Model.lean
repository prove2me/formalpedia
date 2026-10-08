-- Prove2me | Definitions.Def_SchedSurvey_OPmtn_Model
-- name    : SchedSurvey_OPmtn_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T08:32:27.704424+00:00
-- url     : https://prove2.me/theorems/db347e25-b840-45cc-ac01-a1e95f1cf2e6
-- title:
--   §2.1, §2.3, §2.4, §5.2.2, pp. 288–289, 313 — preemptive open-shop schedules, feasibility, loads, C, decrementing sets, constraints (1)–(3), P′
-- statement:
--   This module fixes the model of the problem $O|pmtn|C_{\max}$ of Graham, Lawler, Lenstra and Rinnooy Kan (§2.1–§2.4) and the objects of the algorithm outlined in §5.2.2.
--
--   There are $m$ machines $M_i$ and $n$ jobs $J_j$. In an **open shop** each job $J_j$ consists of operations $O_{1j},\dots,O_{mj}$; operation $O_{ij}$ must be processed on machine $M_i$ for $p_{ij}\ge 0$ time units, in any order. The data form the $m\times n$ matrix $P=(p_{ij})$, rows indexed by machines and columns by jobs. Under **preemption** an operation may be interrupted and resumed later, so a schedule is a finite list of **pieces** $(i,j,s,e)$: machine $M_i$ processes job $J_j$ during $[s,e)$. The module defines:
--
--   1. **Feasibility.** A list of pieces is feasible for $P$ if (a) every piece has $0\le s\le e$ (all jobs are available at time $0$); (b) two pieces on the same machine, or of the same job, do not overlap (each machine processes at most one job at a time, and each job is processed on at most one machine at a time; touching intervals are allowed); (c) for every $(i,j)$ the lengths of the pieces with machine $M_i$ and job $J_j$ add up to exactly $p_{ij}$.
--   2. **Completion by $T$.** Every piece ends by time $T$, i.e. $C_{\max}\le T$.
--   3. **Loads.** The row sum $\sum_j p_{ij}$ (the load of $M_i$) and the column sum $\sum_i p_{ij}$ (the length of $J_j$).
--   4. **The bound $C$.** $C$ is the largest row or column sum:
--   $$C=\max\Big\{\max_j \sum_i p_{ij},\ \max_i \sum_j p_{ij}\Big\}.$$
--   A row $i$ (column $j$) is **tight** if its sum equals $C$, and **slack** otherwise.
--   5. **Decrementing set.** A set $S$ of positions of strictly positive entries of $P$ with exactly one element in each tight row and each tight column, and at most one element in each slack row and each slack column.
--   6. **Constraints (1)–(3) on $\delta$.** (1) If $p_{ij}\in S$ and row $i$ or column $j$ is tight, then $\delta\le p_{ij}$. (2) If $p_{ij}\in S$ and row $i$ (column $j$) is slack, then $\delta\le p_{ij}+C-\sum_k p_{ik}$ ($\delta\le p_{ij}+C-\sum_k p_{kj}$). (3) If row $i$ (column $j$) contains no element of $S$, then $\delta\le C-\sum_k p_{ik}$ ($\delta\le C-\sum_k p_{kj}$). A value of $\delta$ is **maximal** if it satisfies (1)–(3) and every value satisfying them is at most $\delta$.
--   7. **The reduced matrix $P'$**, obtained by replacing each $p_{ij}\in S$ by $\max\{0,p_{ij}-\delta\}$.
--   8. **The partial schedule** of $S$ and $\delta$ started at $t_0$: for each $p_{ij}\in S$, machine $M_i$ processes $J_j$ during $[t_0,\,t_0+\min\{p_{ij},\delta\})$.
--   9. **The joined schedule** of a run of $k$ stages $(P_t,S_t,\delta_t)$: stage $t$ is the partial schedule of $P_t$, $S_t$, $\delta_t$ started at $\delta_0+\dots+\delta_{t-1}$.
--
--   These are the objects of the theorem $C^*_{\max}=C$ for $O|pmtn|C_{\max}$ (Gonzalez and Sahni 1976) and of the decrementing-set algorithm of Lawler and Labetoulle (1978) that constructs an optimal schedule.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$. Processing and start times are real numbers; the survey's §2.2 takes them to be integers, which is a special case. The display defining $C$ on p. 313 prints $\max_i\{\sum_i p_{ij}\}$ for the second term; the next sentence (a row is tight if $\sum_j p_{ij}=C$) shows it means the row sums $\sum_j p_{ij}$, which is what the module uses. "$C$ equals the maximum" is the predicate `IsMaxLoad P C`: every row and column sum is at most $C$ and one of them equals $C$; it determines $C$ whenever $m+n>0$ and is never satisfied when $m=n=0$, so no default value of an empty maximum enters any statement. A piece list may contain several pieces for the same operation (that is preemption) and pieces of length $0$.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), pp. 288–289, §2.1, §2.3, §2.4 (1), (4); p. 313, §5.2.2

import Mathlib

namespace SchedSurvey.OPmtn

/-- A piece of a preemptive open-shop schedule (Graham et al. 1979, §2.3, §2.4 (1), pp. 288–289):
machine `mach` (`Mᵢ`, 0-based) processes job `job` (`Jⱼ`, 0-based) during the interval
`[start, stop)`. Under preemption an operation `O_ij` may be split into several pieces. -/
structure Piece (m n : ℕ) where
  mach : Fin m
  job : Fin n
  start : ℝ
  stop : ℝ

/-- Feasibility of a preemptive open-shop schedule `S` (a list of pieces) for the processing-time
matrix `P` (rows = machines, columns = jobs), §2.1–§2.4, pp. 288–289:
1. every piece starts at a time `≥ 0` (all release dates are `0`, §2.4 (4)) and has
   nonnegative length;
2. a machine processes at most one job at a time and a job is processed on at most one machine
   at a time: two pieces sharing a machine or a job do not overlap (touching is allowed);
3. operation `O_ij` receives exactly `p_ij` units of processing on machine `Mᵢ`: the lengths of
   the pieces with machine `i` and job `j` sum to `P i j`. -/
def IsFeasible {m n : ℕ} (P : Fin m → Fin n → ℝ) (S : List (Piece m n)) : Prop :=
  (∀ q ∈ S, 0 ≤ q.start ∧ q.start ≤ q.stop) ∧
  S.Pairwise (fun q q' => (q.mach = q'.mach ∨ q.job = q'.job) →
    q.stop ≤ q'.start ∨ q'.stop ≤ q.start) ∧
  ∀ i j, ((S.filter (fun q => decide (q.mach = i ∧ q.job = j))).map
    (fun q => q.stop - q.start)).sum = P i j

/-- The schedule `S` completes by time `T`: every piece stops by `T`, i.e. `Cmax ≤ T`. -/
def CompletesBy {m n : ℕ} (S : List (Piece m n)) (T : ℝ) : Prop :=
  ∀ q ∈ S, q.stop ≤ T

/-- Row sum `Σⱼ p_ij`: the total processing required on machine `Mᵢ`. -/
def rowSum {m n : ℕ} (P : Fin m → Fin n → ℝ) (i : Fin m) : ℝ := ∑ j, P i j

/-- Column sum `Σᵢ p_ij`: the total processing time of job `Jⱼ`. -/
def colSum {m n : ℕ} (P : Fin m → Fin n → ℝ) (j : Fin n) : ℝ := ∑ i, P i j

/-- `C = max{maxⱼ Σᵢ p_ij, maxᵢ Σⱼ p_ij}` (§5.2.2, p. 313), stated without a junk maximum:
every row and column sum is at most `C`, and some row or column sum equals `C`. -/
def IsMaxLoad {m n : ℕ} (P : Fin m → Fin n → ℝ) (C : ℝ) : Prop :=
  (∀ i, rowSum P i ≤ C) ∧ (∀ j, colSum P j ≤ C) ∧
  ((∃ i, rowSum P i = C) ∨ ∃ j, colSum P j = C)

/-- A decrementing set (§5.2.2, p. 313): a set `S` of positions of strictly positive entries of
`P`, with exactly one element in each tight row (`Σⱼ p_ij = C`) and each tight column
(`Σᵢ p_ij = C`), and at most one element in each slack row and each slack column. -/
def IsDecrementingSet {m n : ℕ} (P : Fin m → Fin n → ℝ) (C : ℝ)
    (S : Finset (Fin m × Fin n)) : Prop :=
  (∀ x ∈ S, 0 < P x.1 x.2) ∧
  (∀ i, (S.filter (fun x => x.1 = i)).card ≤ 1 ∧
    (rowSum P i = C → (S.filter (fun x => x.1 = i)).card = 1)) ∧
  (∀ j, (S.filter (fun x => x.2 = j)).card ≤ 1 ∧
    (colSum P j = C → (S.filter (fun x => x.2 = j)).card = 1))

/-- The constraints (1), (2), (3) on `δ` (§5.2.2, p. 313), each in its row and column form:
1. if `p_ij ∈ S` and row `i` or column `j` is tight, then `δ ≤ p_ij`;
2. if `p_ij ∈ S` and row `i` (column `j`) is slack, then `δ ≤ p_ij + C − Σₖ p_ik`
   (`δ ≤ p_ij + C − Σₖ p_kj`);
3. if row `i` (column `j`) contains no element of `S`, then `δ ≤ C − Σₖ p_ik`
   (`δ ≤ C − Σₖ p_kj`). -/
def Admissible {m n : ℕ} (P : Fin m → Fin n → ℝ) (C : ℝ) (S : Finset (Fin m × Fin n))
    (δ : ℝ) : Prop :=
  (∀ x ∈ S, (rowSum P x.1 = C ∨ colSum P x.2 = C) → δ ≤ P x.1 x.2) ∧
  (∀ x ∈ S, (rowSum P x.1 ≠ C → δ ≤ P x.1 x.2 + C - rowSum P x.1) ∧
    (colSum P x.2 ≠ C → δ ≤ P x.1 x.2 + C - colSum P x.2)) ∧
  (∀ i, (∀ x ∈ S, x.1 ≠ i) → δ ≤ C - rowSum P i) ∧
  (∀ j, (∀ x ∈ S, x.2 ≠ j) → δ ≤ C - colSum P j)

/-- `δ` is the maximum subject to (1), (2), (3) (§5.2.2, p. 313). -/
def IsMaxAdmissible {m n : ℕ} (P : Fin m → Fin n → ℝ) (C : ℝ) (S : Finset (Fin m × Fin n))
    (δ : ℝ) : Prop :=
  Admissible P C S δ ∧ ∀ δ', Admissible P C S δ' → δ' ≤ δ

open Classical in
/-- The matrix `P′` of §5.2.2, p. 313: each `p_ij ∈ S` is replaced by `max{0, p_ij − δ}`, the
other entries are unchanged. -/
noncomputable def reduce {m n : ℕ} (P : Fin m → Fin n → ℝ) (S : Finset (Fin m × Fin n))
    (δ : ℝ) : Fin m → Fin n → ℝ :=
  fun i j => if (i, j) ∈ S then max 0 (P i j - δ) else P i j

/-- The partial schedule of §5.2.2, p. 313, started at time `t₀`: for each `p_ij ∈ S`, machine
`Mᵢ` processes job `Jⱼ` for `min{p_ij, δ}` units of time, during `[t₀, t₀ + min{p_ij, δ})`. -/
noncomputable def partialSchedule {m n : ℕ} (P : Fin m → Fin n → ℝ)
    (S : Finset (Fin m × Fin n)) (δ t₀ : ℝ) : List (Piece m n) :=
  S.toList.map (fun x => ⟨x.1, x.2, t₀, t₀ + min (P x.1 x.2) δ⟩)

/-- Joining together the partial schedules of successive decrementing sets (§5.2.2, p. 313):
stage `t < k` runs `partialSchedule (Ps t) (Ss t) (δs t)` starting at `δs 0 + ⋯ + δs (t − 1)`. -/
noncomputable def joinSchedule {m n : ℕ} (Ps : ℕ → Fin m → Fin n → ℝ)
    (Ss : ℕ → Finset (Fin m × Fin n)) (δs : ℕ → ℝ) (k : ℕ) : List (Piece m n) :=
  (List.range k).flatMap
    (fun t => partialSchedule (Ps t) (Ss t) (δs t) (∑ s ∈ Finset.range t, δs s))

end SchedSurvey.OPmtn


