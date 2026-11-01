-- Prove2me | Definitions.Def_SelfGuidedALP_WithProbAtLeast
-- name    : SelfGuidedALP_WithProbAtLeast
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:43.405399+00:00
-- url     : https://prove2.me/theorems/ecbdb688-5a90-4af1-a596-bf3a2452981a
-- title:
--   "With a probability of at least $p$"
-- statement:
--   A property of the samples holds **with probability at least** $p$ when some measurable event of probability at least $p$ is contained in the set where the property holds.
--
--   **Formalization Note** This is stronger than an outer-measure bound on a set that may fail to be measurable.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Theorem 2, p.19, and Propositions EC.1, EC.4

import Mathlib

open MeasureTheory

namespace SelfGuidedALP

/-- "`P` holds with probability at least `p`": some **measurable** event of `μ`-mass at least `p` is
contained in `{ω | P ω}` (Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Theorem 2, p.19, and Propositions EC.1, EC.4).

**Formalization Note.** A measurable event inside the set is stronger than an outer-measure bound on a
set that may fail to be measurable. -/
def WithProbAtLeast {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : ℝ) (P : Ω → Prop) :
    Prop :=
  ∃ G : Set Ω, MeasurableSet G ∧ ENNReal.ofReal p ≤ μ G ∧ ∀ ω ∈ G, P ω

end SelfGuidedALP


