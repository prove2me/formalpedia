-- Prove2me | Definitions.Def_SelfGuidedALP_FALPFeasible
-- name    : SelfGuidedALP_FALPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:36.240033+00:00
-- url     : https://prove2.me/theorems/fe0905ef-eea4-43a9-835c-aeaf9e9e88ed
-- title:
--   Constraints (8) of $\mathrm{FALP}_n$
-- statement:
--   A vector $\beta\in\mathbb R^{n+1}$ is **feasible to the constraints (8)** with bases $\theta^1,\dots,\theta^n$ when
--   $$
--   (1-\gamma)\beta_0+\sum_{i=1}^n\beta_i\bigl(\varphi(s;\theta^i)-\gamma\,\mathbb E[\varphi(s';\theta^i)\mid s,a]\bigr)\le c(s,a)\qquad\text{for all }s\in\mathcal S,\ a\in\mathcal A_s .
--   $$
--
--   These say that $V(\cdot;\beta)$ satisfies the constraints (2) of the exact linear program.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.10 and eq. (8), p.16

import Mathlib
import Definitions.Def_SelfGuidedALP_MDP
import Definitions.Def_SelfGuidedALP_RBClass
import Definitions.Def_SelfGuidedALP_feat

open MeasureTheory

namespace SelfGuidedALP

/-- `β ∈ ℝ^{n+1}` is feasible to the constraints (8) of `FALP_n`, formulated with the bases `θs`:
`(1−γ)β₀ + ∑ᵢ βᵢ (ϕ(s;θⁱ) − γ E[ϕ(s';θⁱ) | s,a]) ≤ c(s,a)` for all `(s,a) ∈ 𝒮 × 𝒜ₛ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.10 and eq. (8), p.16). -/
def FALPFeasible {d m n : ℕ} (M : MDP d m) (R : RBClass d)
    (θs : Fin n → EuclideanSpace ℝ (Fin (d + 1))) (β : Fin (n + 1) → ℝ) : Prop :=
  ∀ s ∈ M.S, ∀ a ∈ M.A s,
    (1 - M.γ) * β 0 +
        ∑ i, β i.succ * (feat R.ϕ (θs i) s - M.γ * ∫ s', feat R.ϕ (θs i) s' ∂(M.P s a)) ≤
      M.c s a

end SelfGuidedALP


