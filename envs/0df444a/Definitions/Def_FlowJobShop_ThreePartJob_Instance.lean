-- Prove2me | Definitions.Def_FlowJobShop_ThreePartJob_Instance
-- name    : FlowJobShop_ThreePartJob_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:02:26.671117+00:00
-- url     : https://prove2.me/theorems/0723e991-89a0-484c-b941-e73a334c0e2c
-- title:
--   Lemma 7 — the two-machine job-shop instance constructed from 3-PARTITION
-- statement:
--   Let a 3-PARTITION input have $s=3t$ numbers $a_1,\ldots,a_s$, a target $B>0$, and total $\sum_i a_i=tB$. The reduction constructs a two-machine job shop $JS(C)$ with $s+1$ jobs. For each $1\le i\le s$, job $i$ has two tasks: length $a_i$ on $P_1$, followed by length $a_i$ on $P_2$. Job $s+1$ has $2t$ tasks of length $B$, alternately on $P_2,P_1,P_2,\ldots$. The decision threshold is
--
--   $$\tau=2tB.$$
--
--   This instance and threshold are the common input to the reduction statements in Lemma 7.
--
--   **Formalization Note** Jobs and machines are numbered from zero in Lean. The final job has index $3t$, and its first operation is on machine $1$, representing $P_2$. A valid instance may have $t=0$; then the final job has no operations. Processing times are real casts of the integer input.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 44, proof of Lemma 7, https://doi.org/10.1287/opre.26.1.36

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_ThreePartition
import Definitions.Def_JobShopLTAS_Core_Instance

namespace FlowJobShop.ThreePartJob

open ResourceScheduling.Chain

/-- The two-machine job shop JS constructed in the proof of Lemma 7. Jobs
`j < 3t` each visit machines 0 and 1 for `a j` time. Job `3t`
has `2t` operations of length `b`, alternating between machines 1 and 0. -/
def reductionInstance (C : ThreePartition) : JobShopLTAS.Core.Instance 2 (3 * C.t + 1) where
  μ j := if j.val < 3 * C.t then 2 else 2 * C.t
  π j i := if j.val < 3 * C.t then
      if i.val = 0 then 0 else 1
    else if i.val % 2 = 0 then 1 else 0
  p j _ := if h : j.val < 3 * C.t then (C.a ⟨j.val, h⟩ : ℝ) else (C.b : ℝ)
  p_nonneg j i := by
    split <;> positivity

/-- The finish-time threshold `τ = 2tB` in Lemma 7. -/
def threshold (C : ThreePartition) : ℝ := (2 * C.t * C.b : ℕ)

end FlowJobShop.ThreePartJob


