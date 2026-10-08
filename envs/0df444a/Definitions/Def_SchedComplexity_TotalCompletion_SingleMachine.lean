-- Prove2me | Definitions.Def_SchedComplexity_TotalCompletion_SingleMachine
-- name    : SchedComplexity_TotalCompletion_SingleMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:09.725141+00:00
-- url     : https://prove2.me/theorems/03ee8ef3-f699-4f60-be31-c3e4476e2373
-- title:
--   The problem $n|1|r_n\ge0,w_j=1|\sum w_jC_j$: feasible schedules, processing-order schedules, and its language in the multiplicity encoding
-- statement:
--   **One machine with release dates** (Brucker, Lenstra and Rinnooy Kan, Section 3). There are $n$ jobs $J_1,\dots,J_n$, each consisting of one operation on a single machine. Job $J_j$ has a processing time $p_j$, a weight $w_j$ and a release date $r_j$, all nonnegative integers.
--
--   A **schedule** assigns each job a starting time $B_j\in\mathbb N$; the job then completes at $C_j=B_j+p_j$ and occupies the interval $[B_j, C_j)$. The schedule is **feasible** if
--
--   $$B_j \ge r_j \text{ for every } j, \qquad [B_j, C_j)\cap[B_k, C_k)=\emptyset \text{ for all } j\ne k,$$
--
--   that is, no job starts before its release date and the machine handles at most one job at a time. Idle time is allowed. The criterion is $\sum w_jC_j=\sum_{j=1}^n w_jC_j$.
--
--   A **processing order** (a list of jobs) defines a schedule: the listed jobs are processed in that order, each starting at the later of its release date and the completion time of the previous job of the list.
--
--   The class $n|1|r_n\ge0,w_j=1|\sum w_jC_j$ consists of the instances in which every weight equals $1$ and every job except the last one, $J_n$, has release date $0$ ("a possibly non-zero ready time for one job, say $J_n$"). Its **recognition version** asks, for an instance and a number $y$, whether the instance belongs to the class and has a feasible schedule with $\sum w_jC_j\le y$.
--
--   The language of the problem uses the **multiplicity encoding** of the Remark on p. 23: an instance is written as a list of job types $(c_i, p_i, w_i, r_i)$, $i=1,\dots,k$, standing for $c_i$ identical jobs with data $(p_i,w_i,r_i)$, the types in the order listed. The code is the sequence $k, c_1, p_1, w_1, r_1, \dots, c_k, p_k, w_k, r_k, y$ in binary. A code belongs to the language if the expanded job list is a yes-instance of the recognition version with threshold $y$; class membership is checked on the expanded list.
--
--   These notions make the target of the reduction of Theorem 4(a) precise. The multiplicity encoding is what makes that reduction polynomial: the constructed instance has a number of jobs that is polynomial in the numbers $a_j, b$, hence exponential in the length of their binary codes.
--
--   **Formalization Note** Jobs are indexed by `Fin n` (0-based: index $j$ is the paper's $J_{j+1}$; the last job $J_n$ is index $n-1$). Starting times are natural numbers: the paper computes them from processing orders on integer data (p. 6). Two jobs are disjoint in the half-open-interval sense, so a job with $p_j=0$ occupies no time. A job not listed in a processing order gets starting time $0$. Weights are kept as data (rather than fixed to $1$) so that $w_j=1$ is checked as a class condition, as the paper's notation lists it.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 4 (Section 2, recognition problems), pp. 6–7 (Section 3: data, B_j, C_j, r_n≥0, w_j=1, Σw_jC_j), p. 23 (Remark, multiplicity encoding)

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.TotalCompletion

open ProjSchedTW.Complexity (BSym encNats)

/-! # One machine, release dates, total weighted completion time

Brucker, Lenstra & Rinnooy Kan 1975, Section 3, pp. 6–7: `n` jobs `J_1, …, J_n`, indexed here
by `Fin n` (0-based: index `j` is the paper's `J_{j+1}`), each with one operation on the single
machine, a processing time `p_j`, a weight `w_j` and a release date `r_j`, all nonnegative
integers. -/

variable {n : ℕ}

/-- A schedule with starting times `B : Fin n → ℕ` is feasible when no job starts before its
release date and the machine handles at most one job at a time: job `j` occupies
`[B_j, B_j + p_j)` and two distinct jobs occupy disjoint intervals (a job with `p_j = 0`
occupies the empty interval). Idle time is allowed. Starting times are natural numbers because
the paper computes them from processing orders on integer data (p. 6). -/
def IsFeasible (p r : Fin n → ℕ) (B : Fin n → ℕ) : Prop :=
  (∀ j, r j ≤ B j) ∧
    ∀ j k : Fin n, j ≠ k → ¬ (B j < B k + p k ∧ B k < B j + p j)

/-- The completion time `C_j = B_j + p_j`. -/
def completion (p B : Fin n → ℕ) (j : Fin n) : ℕ :=
  B j + p j

/-- The criterion `Σw_jC_j = Σ_{j=1}^{n} w_j C_j` (p. 7). -/
def sumWC (p w B : Fin n → ℕ) : ℕ :=
  ∑ j : Fin n, w j * completion p B j

/-- The schedule a processing order defines (p. 6, "Given a processing order … we can compute
… the starting time `B_j`"): the jobs of the list `ord` are processed in that order, each as
early as possible, i.e. at the later of its release date and the completion of the previous job
of the list (the first at the later of `0` and its release date). A job not in `ord` gets
starting time `0`; for a job listed twice the last occurrence counts. -/
def orderSchedule (p r : Fin n → ℕ) (ord : List (Fin n)) : Fin n → ℕ :=
  (ord.foldl
    (fun (st : ℕ × (Fin n → ℕ)) j =>
      (max st.1 (r j) + p j, Function.update st.2 j (max st.1 (r j))))
    (0, fun _ => 0)).2

/-- The class `n|1|r_n≥0,w_j=1|Σw_jC_j` (p. 7): all weights equal `1` (`w_j=1`), and every job
except the last one, `J_n` (index `n - 1`), has release date `0` (`r_n≥0`: "a possibly
non-zero ready time for one job, say `J_n`"). -/
def InClass (w r : Fin n → ℕ) : Prop :=
  (∀ j, w j = 1) ∧ ∀ j : Fin n, j.val + 1 < n → r j = 0

/-- The recognition version (Section 2, p. 4) of `n|1|r_n≥0,w_j=1|Σw_jC_j` with threshold `y`:
the instance `(p, w, r)` belongs to the class and some feasible schedule has `Σw_jC_j ≤ y`. -/
def IsYes (p w r : Fin n → ℕ) (y : ℕ) : Prop :=
  InClass w r ∧ ∃ B : Fin n → ℕ, IsFeasible p r B ∧ sumWC p w B ≤ y

/-- The data `(p_j, w_j, r_j)` of one job. -/
structure JobData where
  p : ℕ
  w : ℕ
  r : ℕ

/-- A job type of the multiplicity encoding (Remark, p. 23): `count` identical jobs with
processing time `p`, weight `w` and release date `r`. -/
structure JobType where
  count : ℕ
  p : ℕ
  w : ℕ
  r : ℕ

/-- The job list a list of job types stands for: each type `(c, p, w, r)` contributes `c`
consecutive copies of the job `(p, w, r)`, the types in the order listed. -/
def expand (types : List JobType) : List JobData :=
  types.flatMap fun ty => List.replicate ty.count ⟨ty.p, ty.w, ty.r⟩

/-- The code of an instance in the multiplicity encoding with threshold `y`: the numbers
`k, c_1, p_1, w_1, r_1, …, c_k, p_k, w_k, r_k, y` in binary (`encNats`), where `k` is the number
of job types. The code determines `(types, y)`: separators delimit the numbers, `k` says how
many rows of four follow, and the last number is `y`. -/
def multCode (types : List JobType) (y : ℕ) : List BSym :=
  encNats (types.length :: (types.flatMap fun ty => [ty.count, ty.p, ty.w, ty.r]) ++ [y])

/-- The language of `n|1|r_n≥0,w_j=1|Σw_jC_j` in the multiplicity encoding of the Remark on
p. 23 ("characterizing a subset of jobs with identical data … by its cardinality and a single
copy of the data"): codes `multCode types y` such that the expanded job list `expand types`,
indexed by `Fin (expand types).length` in list order, is a yes-instance (`IsYes`) with
threshold `y`. Class membership (unit weights, release date `0` for every job but the last) is
checked on the expanded list. -/
def sumCLangMult : CookPvsNP.Lang BSym :=
  { x | ∃ (types : List JobType) (y : ℕ),
      IsYes (fun j : Fin (expand types).length => ((expand types).get j).p)
        (fun j => ((expand types).get j).w) (fun j => ((expand types).get j).r) y ∧
      x = multCode types y }

end SchedComplexity.TotalCompletion


