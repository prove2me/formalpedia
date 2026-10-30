-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_IsTruthful
-- name    : SeqPostedPricing_PartitionSPM_IsTruthful
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:03:44.727358+00:00
-- url     : https://prove2.me/theorems/99a0ef6a-f912-4202-9f54-0a875e439c87
-- title:
--   Dominant-strategy truthful mechanism
-- statement:
--   A mechanism $M$ is **truthful** if reporting the true value is a best response for every agent: for almost every value profile $v$ (under the product law $\mu_1 \times \dots \times \mu_n$ of the values), every agent $i$ and every report $w \in \mathbb R$,
--
--   $$
--   u_i\big(v_i; (w, v_{-i})\big) \le u_i(v_i; v).
--   $$
--
--   **Formalization Note** The condition is required for almost every true profile, not at every real profile: types that occur with probability $0$ are not constrained, so every mechanism that is truthful for the agents' possible values is covered (a mechanism defined only on reports in the supports is extended to all real reports by clamping each report to its support). Misreports range over all of $\mathbb R$.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.3 and App. A, Proposition 1 and Theorem 19, pp. 5, 12 (PDF pp. 7, 14)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_utility

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Truthfulness** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.3 and App. A, Proposition 1 and Theorem 19, pp. 5, 12 = PDF pp. 7, 14:
"truthful mechanism"). Reporting the true value is a best response: for almost every value profile
`v` (under the product law `μ_1 × ⋯ × μ_n` of the values), every agent `i` and every misreport
`w ∈ ℝ`, the utility of `i` (true value `v i`) when `i` reports `w` and the others report `v_{-i}` is
at most its utility under truthful reporting.

**Formalization Note** The condition is required for almost every true profile, not at every real
profile: types that occur with probability `0` are not constrained, so every mechanism that is
truthful for the agents' possible values is covered (a mechanism defined only on reports in the
supports is extended to all real reports by clamping each report to its support, an interval for the
regular laws of the paper). Misreports range over all of `ℝ`. -/
def IsTruthful {n : ℕ} (μ : Fin n → Measure ℝ) (M : Mechanism n) : Prop :=
  ∀ᵐ v ∂(Measure.pi μ), ∀ (i : Fin n) (w : ℝ),
    utility M i (v i) (Function.update v i w) ≤ utility M i (v i) v

end SeqPostedPricing.PartitionSPM


