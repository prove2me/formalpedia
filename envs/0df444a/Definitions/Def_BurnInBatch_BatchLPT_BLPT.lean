-- Prove2me | Definitions.Def_BurnInBatch_BatchLPT_BLPT
-- name    : BurnInBatch_BatchLPT_BLPT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:38:30.157928+00:00
-- url     : https://prove2.me/theorems/dec0e789-e1c1-487b-ad4b-b483b2c12f7c
-- title:
--   Algorithm BLPT: full batches of the longest jobs, list-scheduled in nonincreasing order of batch time
-- statement:
--   **Algorithm BLPT** (p. 772) runs in two steps.
--
--   1. Rank the jobs in nonincreasing order of processing time, $p_{j_1} \ge p_{j_2} \ge \dots \ge p_{j_n}$ (equal processing times in any order), and cut the ranked list into successive groups of $B$ jobs:
--   $$B_1 = \{j_1, \dots, j_B\},\quad B_2 = \{j_{B+1}, \dots, j_{2B}\},\ \dots,$$
--   the last group possibly smaller.
--   2. Order these batches in nonincreasing order of batch time $p(B_k)$ (equal times in any order) and assign them to the $m$ machines as they become free: each next batch on the list goes to a machine of currently least load.
--
--   $C(\mathrm{BLPT})$ is the makespan of the resulting schedule, i.e. the largest machine load. For job $j$ in batch $B_k$, its completion time is the load of the machine receiving $B_k$ just before $B_k$, plus $p(B_k)$, and the maximum lateness of the BLPT schedule is $L = \max_j (C_j - d_j)$.
--
--   The algorithm applies Graham's LPT rule to the aggregate jobs obtained from the batch structure of Proposition 2.
--
--   **Formalization Note.** The ranking is any list `l` of all jobs that is nonincreasing in $p$ (`IsLPTList`), its batches are `(l.toChunks B).map List.toFinset` (`blptBatches`), and the ordered batch list is any permutation `bl` of them that is nonincreasing in batch time (`IsBLPTOrder`); theorems quantify over both choices. "As they become free" is the published least-loaded rule `NumStochOpt.ListScheduling.lsLoads` / `listMakespan` (ties to the lowest machine index): with no idle time, the machine that frees up first is a least-loaded one, and the tie rule does not change the multiset of loads. `lsCompletion m q k` is the completion time of item $k$ under that rule ($0$ only if $m = 0$).
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 772, §5, Algorithm BLPT (Steps 1–2); p. 771, Algorithm BLS ("When a machine becomes idle, assign to that machine the batch at the head of the list")

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_BurnInBatch_BatchLPT_Model

namespace BurnInBatch.BatchLPT

open NumStochOpt.ListScheduling

/-- Step 1 of Algorithm BLPT (p. 772), ranking: `l` lists every job exactly once, in
nonincreasing order of processing time (ties in any order). -/
def IsLPTList {n : ℕ} (p : Fin n → ℝ) (l : List (Fin n)) : Prop :=
  l.Perm (List.finRange n) ∧ l.Pairwise (fun a b => p b ≤ p a)

/-- Step 1 of Algorithm BLPT, batching: successive groups of `B` jobs of the ranked list
`l` (the last group possibly smaller). -/
def blptBatches {n : ℕ} (B : ℕ) (l : List (Fin n)) : List (Finset (Fin n)) :=
  (l.toChunks B).map List.toFinset

/-- Step 2 of Algorithm BLPT, ordering: `bl` lists the batches of Step 1, each once, in
nonincreasing order of batch time (equal-time batches in any order). -/
def IsBLPTOrder {n : ℕ} (p : Fin n → ℝ) (B : ℕ) (l : List (Fin n))
    (bl : List (Finset (Fin n))) : Prop :=
  bl.Perm (blptBatches B l) ∧ bl.Pairwise (fun P Q => BurnInBatch.ListSched.batchTime p Q ≤ BurnInBatch.ListSched.batchTime p P)

/-- `C(BLPT)`: the makespan of Step 2, which assigns the ordered batches `bl` to the `m`
machines "as they become free", i.e. each next batch to a least-loaded machine (published
list scheduling `listMakespan`). -/
noncomputable def blptMakespan {n : ℕ} (m : ℕ) (p : Fin n → ℝ) (bl : List (Finset (Fin n))) : ℝ :=
  listMakespan bl.length m (BurnInBatch.ListSched.batchTimes p bl)

/-- Completion time of item `k` under list scheduling of the items `q 0, q 1, …` on `m`
machines: the load of the machine it is assigned to, before it, plus its own time. -/
noncomputable def lsCompletion (m : ℕ) (q : ℕ → ℝ) (k : ℕ) : ℝ :=
  match firstAvailable (lsLoads m q k) with
  | some i => lsLoads m q k i + q k
  | none => 0

/-- `L`, the maximum lateness `max_j (C_j - d_j)` of the BLPT schedule of the ordered
batches `bl`, a job completing with its batch. -/
noncomputable def blptLmax {n : ℕ} (m : ℕ) (p d : Fin n → ℝ) (bl : List (Finset (Fin n))) : ℝ :=
  ⨆ j : Fin n, (jobCompletion bl (fun k => lsCompletion m (BurnInBatch.ListSched.batchTimes p bl) k) j - d j)

end BurnInBatch.BatchLPT


