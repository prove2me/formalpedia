-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_spmOffered
-- name    : SeqPostedPricing_MatroidSPM_spmOffered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:37:25.742983+00:00
-- url     : https://prove2.me/theorems/82b3a5bc-e136-4b8b-85a1-2f188303e85f
-- title:
--   The SPM makes an offer at step $t$
-- statement:
--   At step $t$ the SPM **offers** service to agent $\sigma(t)$ if that agent is one the mechanism makes offers to and $\sigma(t)$ together with the agents served in the earlier steps is feasible. An agent the mechanism would make an offer to but which does not get one is **blocked** by the previously served agents.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.2, unnumbered, p. 4; proof of Theorem 5, p. 6

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_spmServedBefore
open MeasureTheory
open scoped Classical

namespace SeqPostedPricing.MatroidSPM

/-- **The SPM makes an offer at step `t`.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.2, unnumbered, p. 4 (PDF p. 6): "(a) If A ∪ {σ(i)} ∈ J, offer to serve agent σ(i) at
price pi."

`spmOffered Feas p active σ v t`: the agent `σ t` of step `t` is active and can be added
feasibly to the agents served in the steps before `t`. An active agent that is not offered is
**blocked** (§4.1, proof of Theorem 5, p. 6). -/
def spmOffered {n : ℕ} (Feas : Finset (Fin n) → Prop) (p : Fin n → ℝ)
    (active : Finset (Fin n)) (σ : Fin n ≃ Fin n) (v : Fin n → ℝ) (t : Fin n) : Prop :=
  σ t ∈ active ∧ Feas (insert (σ t) (spmServedBefore Feas p active σ v (t : ℕ)))

end SeqPostedPricing.MatroidSPM


