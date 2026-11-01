-- Prove2me | Definitions.Def_SelfGuidedALP_IsStateRelevance
-- name    : SelfGuidedALP_IsStateRelevance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:22.806637+00:00
-- url     : https://prove2.me/theorems/10a0053d-39ed-424a-b273-1595a0981692
-- title:
--   State-relevance distribution $\nu$
-- statement:
--   A **state-relevance distribution** is a probability measure $\nu$ carried by the state space $\mathcal S$. It weighs the states in the objective of the linear programs.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.7

import Mathlib
import Definitions.Def_SelfGuidedALP_MDP

open MeasureTheory

namespace SelfGuidedALP

/-- `ν` is a state-relevance distribution: a probability measure carried by `𝒮`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.7). -/
def IsStateRelevance {d m : ℕ} (M : MDP d m) (ν : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsProbabilityMeasure ν ∧ ν M.S = 1

end SelfGuidedALP


