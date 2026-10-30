-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_spmActive
-- name    : SeqPostedPricing_PartitionSPM_spmActive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:11:24.529052+00:00
-- url     : https://prove2.me/theorems/f0bdf29b-a7e0-423b-af35-a93dfc4e87d1
-- title:
--   Agents offered service by the mechanism $S$
-- statement:
--   For a mechanism $M$, the agents offered service by the mechanism $S$ of §4 are those with $q_i^M > 0$, i.e. served by $M$ with positive probability.
--
--   **Formalization Note** In the paper every agent is offered a price it accepts "with probability exactly $q_i$"; an agent with $q_i = 0$ accepts with probability $0$, so leaving it out changes the outcome only on a null event and changes nothing in $\sum_i p_i q_i$.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, p. 6 (PDF p. 8)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_allocProb

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Agents offered service by the mechanism S** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §4, p. 6 = PDF p. 8: "If offered service,
agent i accepts with probability exactly qi"). The agents that `M` serves with positive probability.

**Formalization Note** Reading 4 of the mission: an agent with `q_i = 0` accepts the paper's offer
with probability `0`, so leaving it out changes the outcome only on a null event; its price is then
unconstrained and it contributes nothing to `Σ_i p_i q_i`. -/
noncomputable def spmActive {n : ℕ} (μ : Fin n → Measure ℝ) (M : Mechanism n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < allocProb μ M i)

end SeqPostedPricing.PartitionSPM


