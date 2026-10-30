-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_allocProb
-- name    : SeqPostedPricing_PartitionSPM_allocProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:05:14.771187+00:00
-- url     : https://prove2.me/theorems/48cc8b66-8fa3-4b9b-9ee6-f424a6f58c7d
-- title:
--   Allocation probability $q_i^M$
-- statement:
--   For independent values $v_i \sim \mu_i$ and a mechanism $M$,
--
--   $$
--   q_i^M = \Pr_{v \sim \mu_1 \times \cdots \times \mu_n}\big[i \in M(v)\big]
--   $$
--
--   is the probability with which $M$ allocates to agent $i$.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2, p. 5 (PDF p. 7)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_Mechanism

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Allocation probability `q_i^M`** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, Lemma 2, p. 5 = PDF p. 7: "q_i^M is the probability
(over v1, · · · , vn) with which M allocates to agent i"). The probability, under the product law of
the values, that agent `i` is served.

**Formalization Note** `toReal` of a probability, so a number in `[0, 1]`; the event is measurable
for admissible mechanisms. -/
noncomputable def allocProb {n : ℕ} (μ : Fin n → Measure ℝ) (M : Mechanism n) (i : Fin n) : ℝ :=
  (Measure.pi μ {v | i ∈ M.alloc v}).toReal

end SeqPostedPricing.PartitionSPM


