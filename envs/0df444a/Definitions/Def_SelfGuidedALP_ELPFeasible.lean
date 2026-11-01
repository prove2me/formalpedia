-- Prove2me | Definitions.Def_SelfGuidedALP_ELPFeasible
-- name    : SelfGuidedALP_ELPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:24.84038+00:00
-- url     : https://prove2.me/theorems/9e52e045-4c0c-4ce8-9b27-c2c22b5165ec
-- title:
--   ELP constraints (2): $V(s)-\gamma\mathbb E[V(s')\mid s,a]\le c(s,a)$
-- statement:
--   A function $V$ is **feasible to the exact linear program** when
--   $$
--   V(s)-\gamma\,\mathbb E[V(s')\mid s,a]\le c(s,a)\qquad\text{for all }s\in\mathcal S,\ a\in\mathcal A_s,
--   $$
--   where $\mathbb E[V(s')\mid s,a]=\int V(s')\,P(\mathrm ds'\mid s,a)$.
--
--   These Bellman inequalities are the constraints every approximate linear program in the mission inherits. Continuous feasible functions lie below $V^*$.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eq. (2), p.7

import Mathlib
import Definitions.Def_SelfGuidedALP_MDP

open MeasureTheory

namespace SelfGuidedALP

/-- `V` is feasible to the exact-linear-program constraints (2):
`V(s) − γ E[V(s') | s,a] ≤ c(s,a)` for all `(s,a) ∈ 𝒮 × 𝒜ₛ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eq. (2), p.7). -/
def ELPFeasible {d m : ℕ} (M : MDP d m) (V : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∀ s ∈ M.S, ∀ a ∈ M.A s, V s - M.γ * ∫ s', V s' ∂(M.P s a) ≤ M.c s a

end SelfGuidedALP


