-- Prove2me | Definitions.Def_SelfGuidedALP_FELPFeasible
-- name    : SelfGuidedALP_FELPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:09.98827+00:00
-- url     : https://prove2.me/theorems/201d5649-6396-4006-ab82-5bd90a3ac4ef
-- title:
--   FELP constraints
-- statement:
--   A pair $(\beta_0,B)$ with $B\in\mathcal B$ is **feasible to the feature-based exact linear program** when
--   $$
--   (1-\gamma)\beta_0+\int_\Theta B(\theta)\bigl(\varphi(s;\theta)-\gamma\,\mathbb E[\varphi(s';\theta)\mid s,a]\bigr)\,\mathrm d\theta\le c(s,a)\qquad\text{for all }s\in\mathcal S,\ a\in\mathcal A_s .
--   $$
--   The constraint $\|B/\rho\|_{2,\rho}<\infty$ is membership in $\mathcal B$.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, FELP, p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_MDP
import Definitions.Def_SelfGuidedALP_Bspace
import Definitions.Def_SelfGuidedALP_feat

open MeasureTheory

namespace SelfGuidedALP

/-- `(β₀, B)` with `B ∈ ℬ` is feasible to the feature-based exact linear program:
`(1−γ)β₀ + ∫_Θ B(θ)(ϕ(s;θ) − γ E[ϕ(s';θ) | s,a]) dθ ≤ c(s,a)` for all `(s,a) ∈ 𝒮 × 𝒜ₛ`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, FELP, p.9). The constraint `‖B/ρ‖_{2,ρ} < ∞` is the type of `B`. -/
def FELPFeasible {d m : ℕ} (M : MDP d m) (R : RBClass d) (β₀ : ℝ) (B : Bspace R) : Prop :=
  ∀ s ∈ M.S, ∀ a ∈ M.A s,
    (1 - M.γ) * β₀ +
        ∫ θ in R.Θ, B θ * (feat R.ϕ θ s - M.γ * ∫ s', feat R.ϕ θ s' ∂(M.P s a)) ≤
      M.c s a

end SelfGuidedALP


