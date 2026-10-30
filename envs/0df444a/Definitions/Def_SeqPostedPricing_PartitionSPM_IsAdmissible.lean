-- Prove2me | Definitions.Def_SeqPostedPricing_PartitionSPM_IsAdmissible
-- name    : SeqPostedPricing_PartitionSPM_IsAdmissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:06:09.499366+00:00
-- url     : https://prove2.me/theorems/100c4041-e0ba-4689-8756-fec2786fff44
-- title:
--   Admissible mechanism for a feasibility constraint
-- statement:
--   Let $\mathcal J$ be a set system on the agents (the feasibility constraint) and let the values be independent with laws $\mu_i$. A mechanism $M$ is **admissible** for $\mathcal J$ if
--
--   1. it always serves a feasible set: $M(v) \in \mathcal J$ for every $v$;
--   2. it is truthful;
--   3. it is individually rational;
--   4. every allocation event $\{v : i \in M(v)\}$ is measurable; and
--   5. every payment $\pi_i$ is integrable under $\mu_1 \times \cdots \times \mu_n$.
--
--   Conditions 4 and 5 make $q_i^M$ and $R^M$ well defined.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.1, p. 4 (PDF p. 6), and App. A, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsTruthful
import Definitions.Def_SeqPostedPricing_PartitionSPM_IsIndividuallyRational

namespace SeqPostedPricing.PartitionSPM

open MeasureTheory in
/-- **Admissible mechanism** (Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.1, p. 4 = PDF p. 6, and App. A, p. 12 = PDF p. 14). A mechanism for
the feasibility constraint `Feas` (the set system `J`) is admissible when it always serves a feasible
set (`M(v) ∈ J`), is truthful and individually rational (for almost every value profile), its allocation events `{v | i ∈ M(v)}` are
measurable, and every payment is integrable under the product law `μ_1 × ⋯ × μ_n`.

**Formalization Note** Measurability and integrability make `q_i^M` and `R^M` honest numbers (a
Bochner integral of a non-integrable function is `0`). -/
def IsAdmissible {n : ℕ} (Feas : Finset (Fin n) → Prop) (μ : Fin n → Measure ℝ) (M : Mechanism n) :
    Prop :=
  (∀ v, Feas (M.alloc v)) ∧ IsTruthful μ M ∧ IsIndividuallyRational μ M ∧
    (∀ i, MeasurableSet {v | i ∈ M.alloc v}) ∧
    (∀ i, Integrable (fun v => M.pay v i) (Measure.pi μ))

end SeqPostedPricing.PartitionSPM


