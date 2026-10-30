-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_spmServedBefore
-- name    : SeqPostedPricing_PartitionSPM_spmServedBefore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:09:17.463599+00:00
-- url     : https://prove2.me/theorems/5ab82698-3860-439a-b9fb-0c80a52a4109
-- title:
--   Agents served in the first $t$ steps of an SPM
-- statement:
--   Fix an ordering $\sigma$ of the agents. Starting from $A = \emptyset$, the SPM runs one step for each of the agents $\sigma(1), \sigma(2), \dots$ in turn. The set of agents served after the first $t$ steps is the resulting $A$; after all $n$ steps it is the set of agents finally served.
--
--   **Formalization Note** Steps are numbered from $0$: `σ t` is the agent of the paper's step $t + 1$.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_spmStep

namespace SeqPostedPricing.PartitionSPM

/-- **Agents served in the first `t` steps of an SPM** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, p. 4 = PDF p. 6: "1. Initialize
A ← ∅. 2. For i = 1 through n, do: …"). Starting from `A = ∅`, run `spmStep` on the agents
`σ 0, σ 1, …, σ (t − 1)` in turn. `spmServedBefore … n` is the set `A` of agents finally served
(step 3).

**Formalization Note** `σ : Fin n ≃ Fin n` maps the step `t` (0-based) to the agent offered at that
step, the paper's `σ(t + 1)`. -/
noncomputable def spmServedBefore {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (σ : Fin n ≃ Fin n) (v : Fin n → ℝ) (t : ℕ) : Finset (Fin n) :=
  ((List.ofFn (fun s => σ s)).take t).foldl (spmStep Feas p active v) ∅

end SeqPostedPricing.PartitionSPM


