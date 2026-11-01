-- Prove2me | Definitions.Def_SelfGuidedALP_FALPSGFeasible
-- name    : SelfGuidedALP_FALPSGFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:47.772278+00:00
-- url     : https://prove2.me/theorems/7e6e73e8-4e87-40af-b9ef-cacd2a5cecf7
-- title:
--   Constraints (8)–(9) of $\mathrm{FALP}^{\mathrm{SG}}_n$
-- statement:
--   A vector $\beta\in\mathbb R^{n+1}$ is **feasible to** $\mathrm{FALP}^{\mathrm{SG}}_n$ with previous VFA $V_{\mathrm{prev}}$ when it satisfies (8) and the guiding constraints
--   $$
--   \beta_0+\sum_{i=1}^n\beta_i\,\varphi(s;\theta^i)\ge V_{\mathrm{prev}}(s)\qquad\text{for all }s\in\mathcal S.\tag{9}
--   $$
--
--   The guiding constraints force the new VFA to dominate the previous one at every state.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eqs. (8)–(9), p.16

import Mathlib
import Definitions.Def_SelfGuidedALP_FALPFeasible
import Definitions.Def_SelfGuidedALP_vfa

namespace SelfGuidedALP

/-- `β` is feasible to `FALP^SG_n` with previous VFA `Vprev`: it satisfies (8) and the guiding
constraints (9), `β₀ + ∑ᵢ βᵢ ϕ(s;θⁱ) ≥ Vprev(s)` for all `s ∈ 𝒮`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, eqs. (8)–(9), p.16). -/
def FALPSGFeasible {d m n : ℕ} (M : MDP d m) (R : RBClass d)
    (θs : Fin n → EuclideanSpace ℝ (Fin (d + 1))) (Vprev : EuclideanSpace ℝ (Fin d) → ℝ)
    (β : Fin (n + 1) → ℝ) : Prop :=
  FALPFeasible M R θs β ∧ ∀ s ∈ M.S, Vprev s ≤ vfa R θs β s

end SelfGuidedALP


