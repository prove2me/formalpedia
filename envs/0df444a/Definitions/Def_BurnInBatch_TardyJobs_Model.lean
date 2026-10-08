-- Prove2me | Definitions.Def_BurnInBatch_TardyJobs_Model
-- name    : BurnInBatch_TardyJobs_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:43.404448+00:00
-- url     : https://prove2.me/theorems/64b520aa-ad67-40fe-93a0-9e57a6f92abf
-- title:
--   §2 and §4: single batch machine, schedules, and tardy-job objective
-- statement:
--   A single batch machine processes $n$ jobs. Job $j$ has processing time $p_j$, release time $r_j$, and due date $d_j$. A batch is a nonempty set of at most $B$ jobs. Its duration is the maximum processing time of its members, and it starts when both the previous batch has finished and every member has been released. A valid schedule is an ordered list of disjoint batches that covers all jobs. For a schedule $S$, job $j$ completes at its batch completion time $C_j(S)$; the number of tardy jobs and its optimum are
--
--   $$
--   U(S)=\#\{j:d_j<C_j(S)\},\qquad U^*=\min_{S\text{ valid}}U(S).
--   $$
--
--   The model also names batch-EDD order (earlier batches have no later due date than jobs in subsequent batches), index-consecutive batches, and optimal schedules. These are the common objects of both structural lemmas and both dynamic programs.
--
--   **Formalization Note** Jobs are `Fin n`, indexed from zero. Times are natural numbers. The schedule starts each batch as soon as release times and the previous completion permit. Even tardy jobs must appear in a valid schedule. The empty instance has the empty valid schedule.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 766, §2, Assumptions 1–3; p. 767, Definition 1; p. 770, §4

import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model
import Definitions.Def_BurnInBatch_ReleaseTmax_Model

namespace BurnInBatch.TardyJobs

/-- A batch is nonempty and has no more than `B` jobs. -/
def ValidBatch {n : ℕ} (B : ℕ) (P : Finset (Fin n)) : Prop :=
  P.Nonempty ∧ P.card ≤ B

/-- A complete one-machine batch schedule, in processing order. -/
def ValidSchedule {n : ℕ} (B : ℕ) (S : List (Finset (Fin n))) : Prop :=
  (∀ P ∈ S, ValidBatch B P) ∧
  S.Pairwise (fun P Q => Disjoint P Q) ∧
  ∀ j : Fin n, ∃ P ∈ S, j ∈ P

/-- Process a list of batches as early as their releases and the preceding batch permit. -/
def finish {n : ℕ} (p r : Fin n → ℕ) : List (Finset (Fin n)) → ℕ → ℕ
  | [], t => t
  | P :: S, t => finish p r S (max t (BurnInBatch.ReleaseTmax.batchRelease r P) + BurnInBatch.AgreeTmax.batchTime p P)

/-- Completion time of job `j`. This is used only for complete valid schedules. -/
def jobCompletionAux {n : ℕ} (p r : Fin n → ℕ) (j : Fin n) :
    List (Finset (Fin n)) → ℕ → ℕ
  | [], _ => 0
  | P :: S, t =>
      let t' := max t (BurnInBatch.ReleaseTmax.batchRelease r P) + BurnInBatch.AgreeTmax.batchTime p P
      if j ∈ P then t' else jobCompletionAux p r j S t'

def jobCompletion {n : ℕ} (p r : Fin n → ℕ)
    (S : List (Finset (Fin n))) (j : Fin n) : ℕ :=
  jobCompletionAux p r j S 0

/-- The number of jobs completed strictly after their due dates. -/
def tardyCount {n : ℕ} (p r d : Fin n → ℕ)
    (S : List (Finset (Fin n))) : ℕ :=
  (Finset.univ.filter (fun j => d j < jobCompletion p r S j)).card

/-- The minimum number of tardy jobs over all complete valid batch schedules. -/
noncomputable def minTardy {n : ℕ} (B : ℕ) (p r d : Fin n → ℕ) : ℕ :=
  sInf { v : ℕ | ∃ S : List (Finset (Fin n)), ValidSchedule B S ∧ tardyCount p r d S = v }

/-- Definition 1: earlier batches contain no job with a later due date than a job
in a later batch. -/
def BatchEDD {n : ℕ} (d : Fin n → ℕ) (S : List (Finset (Fin n))) : Prop :=
  ∀ a b : Fin S.length, a < b →
    ∀ i ∈ S[a], ∀ j ∈ S[b], d i ≤ d j

/-- A batch contains an interval of job indices in the given index order. -/
def Consecutive {n : ℕ} (P : Finset (Fin n)) : Prop :=
  ∃ first : ℕ, ∀ j : Fin n, j ∈ P ↔ first ≤ j.val ∧ j.val < first + P.card

/-- An optimal complete batch schedule for the number of tardy jobs. -/
def Optimal {n : ℕ} (B : ℕ) (p r d : Fin n → ℕ)
    (S : List (Finset (Fin n))) : Prop :=
  ValidSchedule B S ∧ tardyCount p r d S = minTardy B p r d

/-- The paper's equal-duration data: every job has processing time `p`. -/
def equalTime {n : ℕ} (p : ℕ) : Fin n → ℕ := fun _ => p

end BurnInBatch.TardyJobs


