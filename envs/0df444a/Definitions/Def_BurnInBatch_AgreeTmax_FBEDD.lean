-- Prove2me | Definitions.Def_BurnInBatch_AgreeTmax_FBEDD
-- name    : BurnInBatch_AgreeTmax_FBEDD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:07:51.010365+00:00
-- url     : https://prove2.me/theorems/3b76158f-a8ef-4b1f-b5e8-4627fd007203
-- title:
--   Algorithm FBEDD (Full-Batch EDD), p. 769
-- statement:
--   **Algorithm FBEDD** (Full-Batch EDD) of Lee, Uzsoy and Martin-Vega builds a batch schedule of the jobs $1,\dots,n$ on a machine of capacity $B\ge 1$:
--
--   1. successively group the $B$ jobs with the smallest indices into batches, so that batch $k$ ($k=1,2,\dots$) consists of the jobs $(k-1)B+1,\dots,\min\{kB,n\}$; only the last batch may hold fewer than $B$ jobs;
--   2. process the batches in this order, the batch with the lowest-indexed jobs first.
--
--   There are $\lceil n/B\rceil$ batches. When jobs are indexed in increasing order of due dates, the resulting sequence is in batch-EDD order.
--
--   **Formalization Note** Jobs are 0-based (`Fin n`): batch $k$ ($k=0,1,\dots,\lceil n/B\rceil-1$) is the set of indices in $[kB,(k+1)B)$. The number of batches is written $(n+B-1)/B$ with natural-number division, which is $\lceil n/B\rceil$ for $B\ge 1$.
-- source:
--   Lee, Uzsoy & Martin-Vega, Efficient Algorithms for Scheduling Semiconductor Burn-In Operations, Oper. Res. 40(4) (1992), p. 769, Algorithm FBEDD (Full-Batch EDD)

import Mathlib

namespace BurnInBatch.AgreeTmax

/-- Algorithm FBEDD (Full-Batch EDD) of Lee, Uzsoy & Martin-Vega (1992), p. 769: group the `B`
jobs with the smallest indices into a batch, the next `B` into the next, and so on (the last batch
may hold fewer than `B` jobs), and process the batches in this order. Batch `k` (0-based) is the
set of jobs with 0-based index in `[k B, (k + 1) B)`; there are `⌈n / B⌉` batches. -/
def fbedd (n B : ℕ) : List (Finset (Fin n)) :=
  (List.range ((n + B - 1) / B)).map fun k =>
    Finset.univ.filter fun i : Fin n => k * B ≤ i.val ∧ i.val < (k + 1) * B

end BurnInBatch.AgreeTmax


