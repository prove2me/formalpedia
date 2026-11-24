-- Prove2me | Definitions.Def_UnfairML_Coverage_Supplement_GeneralCoverage
-- name    : UnfairML_Coverage_Supplement_GeneralCoverage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:38:12.823671+00:00
-- url     : https://prove2.me/theorems/adc6f53b-60a3-4e10-b263-762b37eb3289
-- title:
--   Eqs. (19)–(20) — protected coverage under a general fairness notion and the printed risk threshold r̂
-- statement:
--   On the general-fairness branch $c_p=1-\theta\gamma_r s$ of §5, the protected group's coverage rate (19) at effort $s$ is
--   $$\phi_p(\theta,s)=\frac{\theta\gamma_r s}{1-\gamma_p s}.$$
--   For efforts $s_1=s^*(1)$ and $s_\theta=s^*(\theta)$, the risk threshold printed above (20) on p. 28 is
--   $$A_2=\frac{\theta^2 s_\theta^2}{s_1^2},\qquad B_2=\frac{1-\gamma_r s_\theta}{1-\gamma_r s_1},\qquad
--   \hat r=\frac{\gamma_r(A_2-\theta B_2)}{(\gamma_r-\gamma_p)A_2-(\theta\gamma_r-\gamma_p)B_2}.$$
--   The efforts are arguments, so that Theorem 5 can be evaluated at any optimal efforts.
--
--   **Formalization Note** $B_2$ is unsquared, exactly as printed; the denominator's bare $B_2$ is read as $B_2(\theta)$. Real division is total in Lean ($x/0=0$); the only use of $\hat r$ in this mission is at a witness where every denominator is nonzero.
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), pp. 27–28, eqs. (19)–(20)

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_GeneralFairness

namespace UnfairML.Coverage.Supplement

/-- The protected coverage rate (19), p. 27, on the branch `cp = 1 - θ*γr*s`:
`φp(θ) = θ γr s / (1 − γp s)` evaluated at an effort `s`. -/
noncomputable def protCoverageGeneral (P : Params) (θ s : ℝ) : ℝ :=
  θ * P.γr * s / (1 - P.γp * s)

/-- The risk threshold `r̂` printed above (20), p. 28, with `s₁ = s*(1)` and `sθ = s*(θ)`:
`A₂ = θ² sθ² / s₁²`, `B₂ = (1 − γr sθ)/(1 − γr s₁)` (unsquared, as printed) and
`r̂ = γr (A₂ − θ B₂) / ((γr − γp) A₂ − (θ γr − γp) B₂)`. -/
noncomputable def rhat (P : Params) (θ s₁ sθ : ℝ) : ℝ :=
  let A₂ := θ ^ 2 * sθ ^ 2 / s₁ ^ 2
  let B₂ := (1 - P.γr * sθ) / (1 - P.γr * s₁)
  P.γr * (A₂ - θ * B₂) / ((P.γr - P.γp) * A₂ - (θ * P.γr - P.γp) * B₂)

end UnfairML.Coverage.Supplement


