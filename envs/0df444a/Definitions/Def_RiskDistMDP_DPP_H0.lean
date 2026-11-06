-- Prove2me | Definitions.Def_RiskDistMDP_DPP_H0
-- name    : RiskDistMDP_DPP_H0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:13.903066+00:00
-- url     : https://prove2.me/theorems/4a96b738-f3c6-4116-a3e6-e574830934a7
-- title:
--   Time-0 functional $H_0v=\sigma_0(\widetilde P^v_0)$ (3.1)
-- statement:
--   For $v\in\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$, let $\widetilde P^v_0$ be the law of $\gamma v(Y)$ with $Y\sim\mu$, the initial law. Then
--   $$H_0v:=\sigma_0\big(\widetilde P^v_0\big).$$
--   It turns a value function at time 1 into the time-0 value of the problem.
--
--   **Formalization Note** The page writes $Y\sim\xi_1$; $\xi_1$ is defined nowhere and is read as $\mu$, the law of $X_1$. The value is kept in `EReal`, because $\sigma_0$ is not covered by Assumption 2.6 or normalization and may be $+\infty$.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (3.1), p. 14

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_RiskMDP

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The law `P̃^v_0` of arXiv:2203.09612v4, (3.1), p.14: the distribution of `γ v(Y)` with
`Y ∼ μ`.

**Formalization Note** The page writes `Y ∼ ξ₁`; `ξ₁` is defined nowhere, and is read as `μ`, the
law of `X₁` (Assumption 2.11 (i)) — reading R3. -/
noncomputable def lawH0 {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (v : 𝕏 → ℝ) : Measure ℝ :=
  (R.μ : Measure 𝕏).map fun y => R.γ * v y

/-- The functional `H₀ v := σ₀(P̃^v_0)` of arXiv:2203.09612v4, (3.1), p.14.

**Formalization Note** The page types it `ℓ^∞(𝕏, ℬ(𝕏)) → ℝ`; it is kept in `EReal` because
`σ₀` is not covered by Assumption 2.6 and may take the value `+∞` (correction C5). -/
noncomputable def H0 {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (v : 𝕏 → ℝ) : EReal :=
  R.σ0 (lawH0 R v)

end RiskDistMDP.DPP


