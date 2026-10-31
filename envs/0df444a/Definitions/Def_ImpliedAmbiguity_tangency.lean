-- Prove2me | Definitions.Def_ImpliedAmbiguity_tangency
-- name    : ImpliedAmbiguity_tangency
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:06.301031+00:00
-- url     : https://prove2.me/theorems/3f1b8830-011d-4236-9a12-e9842f3e72f9
-- title:
--   Tangency portfolio $\bar x = \Sigma_R^{-1}(\mu - R_f\mathbf 1)$
-- statement:
--   The **tangency portfolio** is
--
--   $$
--   \bar x = \Sigma_R^{-1}(\mu - R_f\mathbf 1),
--   $$
--
--   the portfolio of risky assets with the highest Sharpe ratio. The ratio $\mathrm{Sr}(x)/\mathrm{Sr}(\bar x)$ is the normalized Sharpe ratio of $x$.
--
--   **Formalization Note** $\Sigma_R^{-1}$ is Mathlib's matrix inverse, the true inverse for positive definite $\Sigma_R$.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), §4.3, p.21 (definition of x̄)

import Mathlib

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
§4.3, p.21: the tangency portfolio `x̄ ≡ Σ_R⁻¹(µ − R_f1)`.

**Formalization Note.** The excess return vector is passed as `c`; `Σ_R⁻¹` is Mathlib's matrix
inverse, the true inverse for positive definite `SigmaR` (assumed in every theorem). -/
noncomputable def tangency {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) :
    Fin N → ℝ :=
  SigmaR⁻¹ *ᵥ c

end ImpliedAmbiguity


