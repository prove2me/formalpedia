-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_IsOptimal
-- name    : SeqPostedPricing_PartitionSPM_IsOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:05.930959+00:00
-- url     : https://prove2.me/theorems/caf46d31-7c77-4f5f-aa7b-f960d19bdc80
-- title:
--   Revenue-optimal mechanism
-- statement:
--   A mechanism $M$ is **optimal** for the feasibility constraint $\mathcal J$ and the value laws $\mu_i$ if it is admissible and
--
--   $$
--   R^A \le R^M \quad \text{for every admissible mechanism } A.
--   $$
--
--   By Theorem 19 of the paper ($R^{\mathcal M} \ge R^A$ for every truthful mechanism $A$), Myerson's mechanism is optimal in this sense.
--
--   **Formalization Note** The mission's results about "Myerson's mechanism" are stated for every optimal mechanism, which includes Myerson's mechanism.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, App. A, Theorem 19, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsAdmissible
import Definitions.Def_SeqPostedPricing_PartitionSPM_revenue

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Revenue-optimal mechanism** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, App. A, Theorem 19, p. 12 = PDF p. 14: "R^M ≥ R^A for every
truthful mechanism A", where M is Myerson's mechanism). `M` is admissible for `Feas` and its expected
revenue is at least that of every admissible mechanism.

**Formalization Note** Reading 1 of the mission: the paper's results about "Myerson's mechanism" are
stated for every optimal admissible mechanism. Myerson's mechanism is one (Theorem 19); it is
deterministic, dominant-strategy truthful, ex-post individually rational (so in particular almost
everywhere), feasible, and its threshold payments are integrable. -/
def IsOptimal {n : ℕ} (Feas : Finset (Fin n) → Prop) (μ : Fin n → Measure ℝ) (M : Mechanism n) :
    Prop :=
  IsAdmissible Feas μ M ∧ ∀ A : Mechanism n, IsAdmissible Feas μ A → revenue μ A ≤ revenue μ M

end SeqPostedPricing.PartitionSPM


