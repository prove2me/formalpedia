-- Prove2me | Definitions.Def_ImpliedAmbiguity_vTheta
-- name    : ImpliedAmbiguity_vTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:12.151883+00:00
-- url     : https://prove2.me/theorems/9feae234-616a-43fd-87cb-3053872f0154
-- title:
--   The vector $v^\theta = \theta^{-1}\Sigma_R^{-1}(\mu-R_f\mathbf 1) - x$
-- statement:
--   Let $\Sigma_R$ be a positive definite covariance matrix, $c = \mu - R_f\mathbf 1$ the expected excess return vector, $x\in\mathbb R^N$ a portfolio and $\theta > 0$. Define
--
--   $$
--   v^\theta = \frac1\theta\,\Sigma_R^{-1} c - x. \tag{17}
--   $$
--
--   $v^\theta$ is the difference between the mean-variance optimal portfolio of a pure risk-averse investor with coefficient $\theta$ and the given portfolio $x$; it spans the rank-one second-order belief $\Sigma_M^\theta$ and enters the implied coefficient of ambiguity aversion $\eta^\theta$.
--
--   **Formalization Note** $\Sigma_R^{-1}$ is Mathlib's matrix inverse, the true inverse for positive definite $\Sigma_R$. The function is total in $\theta\in\mathbb R$; the paper uses $\theta>0$.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), eq. (17), p.18; Appendix C, Lemma 4, p.41

import Mathlib

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
eq. (17), p.18: `v^θ = (1/θ) Σ_R⁻¹ (µ − R_f 1) − x`; Appendix C, Lemma 4, p.41: `v^θ = (1/θ) Σ⁻¹c − x`.

**Formalization Note.** The excess return vector is passed as `c` (instantiated with
`excessReturn μ Rf` in Theorems 3–4). `Σ_R⁻¹` is Mathlib's matrix inverse `SigmaR⁻¹`, which is
the true inverse whenever `SigmaR` is positive definite (as every theorem assumes). The
function is total in `θ : ℝ`; the paper uses it for `θ > 0`. -/
noncomputable def vTheta {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (c x : Fin N → ℝ) (θ : ℝ) :
    Fin N → ℝ :=
  (1 / θ) • (SigmaR⁻¹ *ᵥ c) - x

end ImpliedAmbiguity


