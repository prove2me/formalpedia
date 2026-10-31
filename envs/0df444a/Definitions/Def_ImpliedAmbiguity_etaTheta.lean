-- Prove2me | Definitions.Def_ImpliedAmbiguity_etaTheta
-- name    : ImpliedAmbiguity_etaTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:51.53504+00:00
-- url     : https://prove2.me/theorems/993fbcc9-be56-45ca-960d-fce3655dde23
-- title:
--   The implied coefficient of relative ambiguity aversion $\eta^\theta$
-- statement:
--   With $\Sigma_R$, $c = \mu-R_f\mathbf 1$, $x$ and $v^\theta$ as in (17), define
--
--   $$
--   \eta^\theta = \frac{(v^\theta)^\top \Sigma_R v^\theta}{x^\top \Sigma_R v^\theta}. \tag{19}
--   $$
--
--   It is the least coefficient of relative ambiguity aversion with which $x$ is optimal for an investor with absolute risk aversion $\theta$ (Theorems 2 and 3); Theorem 4 minimizes it over $\theta\in(0,\bar\theta)$.
--
--   **Formalization Note** $\eta^\theta$ is a total function of $\theta\in\mathbb R$ (Lean's $a/0 = 0$). Under $c^\top x>0$ and $0<\theta<\bar\theta$ the denominator is positive, and Theorem 4 minimizes over exactly the open interval $(0,\bar\theta)$.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), eq. (19), p.19

import Mathlib
import Definitions.Def_ImpliedAmbiguity_vTheta

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
eq. (19), p.19: the coefficient of relative ambiguity aversion
`η^θ = (v^θ)ᵀΣ_R v^θ / xᵀΣ_R v^θ`, with `v^θ` as in (17).

**Formalization Note.** `η^θ` is a total function of `θ : ℝ` (Lean's `a/0 = 0`). The paper
defines (19) under `v^θ ≠ 0`; under (14) and `0 < θ < θ̄` the denominator `xᵀΣ_R v^θ` is
positive, and Theorem 4 minimizes `η^θ` over exactly the open interval `(0, θ̄)`. -/
noncomputable def etaTheta {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (c x : Fin N → ℝ) (θ : ℝ) :
    ℝ :=
  (vTheta SigmaR c x θ ⬝ᵥ (SigmaR *ᵥ vTheta SigmaR c x θ)) /
    (x ⬝ᵥ (SigmaR *ᵥ vTheta SigmaR c x θ))

end ImpliedAmbiguity


