-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_spmOffered
-- name    : SeqPostedPricing_PartitionSPM_spmOffered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:10:05.168559+00:00
-- url     : https://prove2.me/theorems/1122ab19-592f-4949-b526-351a268831d0
-- title:
--   The SPM offers service at a step
-- statement:
--   At step $t$ the SPM **offers service** to agent $\sigma(t)$ if that agent is active and adding it to the set of agents served in the earlier steps is feasible.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, step 2(a), p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_spmServedBefore

namespace SeqPostedPricing.PartitionSPM

/-- **The SPM offers service at step `t`** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, p. 4 = PDF p. 6, step 2(a): "If
A ∪ {σ(i)} ∈ J, offer to serve agent σ(i) at price pi"). The agent `σ t` is active and adding it to
the set served in the first `t` steps is feasible.

**Formalization Note** Steps are 0-based; see `spmServedBefore`. -/
def spmOffered {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ) (active : Finset (Fin n))
    (σ : Fin n ≃ Fin n) (v : Fin n → ℝ) (t : Fin n) : Prop :=
  σ t ∈ active ∧ Feas (insert (σ t) (spmServedBefore Feas p active σ v t))

end SeqPostedPricing.PartitionSPM


