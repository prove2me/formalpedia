-- Prove2me | Definitions.Def_MooreLateJobs_NumLate_MooreStep
-- name    : MooreLateJobs_NumLate_MooreStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:05:35.008994+00:00
-- url     : https://prove2.me/theorems/11625ec7-c308-44fe-ad6a-f4ed786b01fa
-- title:
--   One pass of Steps 2-3 of Moore's algorithm
-- statement:
--   The state of Moore's algorithm is a pair (current sequence, list of rejected jobs). One pass of Steps 2–3 transforms a state as follows.
--
--   1. (Step 2) Find the first late job $J_{i_q}$ of the current sequence $(J_{i_1},\dots,J_{i_n})$: $J_{i_q}$ is late and $J_{i_1},\dots,J_{i_{q-1}}$ are early.
--   2. (Step 3) Reorder $J_{i_1},\dots,J_{i_q}$ according to the due-date rule, producing
--   $$
--   J_{l_1}\cdots J_{l_q},\;J_{i_{q+1}}\cdots J_{i_n}\qquad\text{where } D_{l_1}\le\cdots\le D_{l_q}.
--   $$
--      - Case 1): if all jobs of $J_{l_1}\cdots J_{l_q}$ are early (in that subsequence), the whole sequence becomes the current sequence and nothing is rejected.
--      - Case 2): otherwise the job $J_{i_q}$ is rejected (appended to the rejected list) and removed, and the remaining sequence becomes the current sequence.
--
--   Steps 1–3 of the algorithm are: start from a shortest-processing-time ordering of the jobs with no rejected jobs, and repeat this pass until the current sequence has no late job.
--
--   **Formalization Note** The relation holds for **every** due-date ordering of the prefix (ties are broken arbitrarily), so it is a relation, not a function. Positions are 0-based: $q$ indexes the first late job and the reordered prefix is a permutation of the first $q+1$ entries. The first late job is determined by positional completion times; lateness inside the reordered prefix uses the late set of that prefix.
-- source:
--   Moore, An n Job, One Machine Sequencing Algorithm for Minimizing the Number of Late Jobs, Management Science 15(1), 1968, p. 103, The Algorithm, Steps 2-3

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_MooreLateJobs_NumLate_lateSet

namespace MooreLateJobs.NumLate

/-- One pass of Steps 2–3 of Moore's algorithm (p. 103), on states `(cur, rej)` = (current
sequence, list of rejected jobs in order of rejection).

`MooreStep t D (cur, rej) (cur', rej')` holds iff, with `q` the (0-based) position of the first
late job `J_{i_q}` of the current sequence (Step 2), and `pre'` a re-ordering of the prefix
`J_{i_1} ⋯ J_{i_q}` (the first `q + 1` jobs, the late job included) according to the due-date rule
(Step 3, ties broken arbitrarily), either
1) every job of `pre'` is early in `pre'`, and the new current sequence is `pre'` followed by the
   rest `J_{i_{q+1}} ⋯ J_{i_n}` of the current sequence, nothing rejected; or
2) some job of `pre'` is late in `pre'`, the job `J_{i_q}` is rejected (appended to `rej`) and
   removed from `pre'`, and the new current sequence is the rest of `pre'` followed by
   `J_{i_{q+1}} ⋯ J_{i_n}`. -/
def MooreStep {ι : Type*} [DecidableEq ι] (t D : ι → ℝ) (s s' : List ι × List ι) : Prop :=
  ∃ (q : ℕ) (hq : q < s.1.length),
    D (s.1[q]'hq) < Shared.completionAt t s.1 q ∧
    (∀ (k : ℕ) (hk : k < q), Shared.completionAt t s.1 k ≤ D (s.1[k]'(lt_trans hk hq))) ∧
    ∃ pre' : List ι, pre'.Perm (s.1.take (q + 1)) ∧ pre'.Pairwise (fun a b => D a ≤ D b) ∧
      ((lateSet t D pre' = ∅ ∧ s' = (pre' ++ s.1.drop (q + 1), s.2)) ∨
       ((lateSet t D pre').Nonempty ∧
          s' = (pre'.erase (s.1[q]'hq) ++ s.1.drop (q + 1), s.2 ++ [s.1[q]'hq])))

end MooreLateJobs.NumLate


