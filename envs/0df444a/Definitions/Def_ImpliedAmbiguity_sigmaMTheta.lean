-- Prove2me | Definitions.Def_ImpliedAmbiguity_sigmaMTheta
-- name    : ImpliedAmbiguity_sigmaMTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:06:19.236985+00:00
-- url     : https://prove2.me/theorems/e74cff42-3104-4202-beef-6a3ca862cec2
-- title:
--   The rank-one second-order belief $\Sigma_M^\theta$
-- statement:
--   With $\Sigma_R$, $c = \mu-R_f\mathbf 1$, $x$ and $v^\theta$ as in (17), define the $N\times N$ matrix
--
--   $$
--   \Sigma_M^\theta = \frac{1}{(v^\theta)^\top \Sigma_R v^\theta}\,\bigl(\Sigma_R v^\theta\bigr)\bigl(\Sigma_R v^\theta\bigr)^\top. \tag{18}
--   $$
--
--   It is the smallest second-order belief (covariance of the expected returns attributed to model uncertainty) compatible with the optimality of $x$ at risk aversion $\theta$.
--
--   **Formalization Note** $(\Sigma_R v)(\Sigma_R v)^\top$ is `vecMulVec`. The paper defines (18) only when $v^\theta\neq 0$; the Lean function is total (it is the zero matrix when $v^\theta = 0$, because Lean's $1/0 = 0$), and Theorem 3 assumes $v^\theta \neq 0$ as the paper does.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), eq. (18), p.19

import Mathlib
import Definitions.Def_ImpliedAmbiguity_vTheta

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
eq. (18), p.19: the rank-one second-order belief
`Σ^θ_M = (1/((v^θ)ᵀΣ_R v^θ)) (Σ_R v^θ)(Σ_R v^θ)ᵀ`, with `v^θ` as in (17).

**Formalization Note.** `(Σ_R v)(Σ_R v)ᵀ` is `vecMulVec (SigmaR *ᵥ v) (SigmaR *ᵥ v)`. The paper
defines (18) only when `v^θ ≠ 0` (p.19); the Lean function is total (Lean's `1/0 = 0` gives the
zero matrix at `v^θ = 0`), and Theorem 3 assumes `v^θ ≠ 0` as the paper does. -/
noncomputable def sigmaMTheta {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (c x : Fin N → ℝ)
    (θ : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  (1 / (vTheta SigmaR c x θ ⬝ᵥ (SigmaR *ᵥ vTheta SigmaR c x θ))) •
    vecMulVec (SigmaR *ᵥ vTheta SigmaR c x θ) (SigmaR *ᵥ vTheta SigmaR c x θ)

end ImpliedAmbiguity


