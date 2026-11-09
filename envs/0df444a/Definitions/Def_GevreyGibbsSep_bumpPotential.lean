-- Prove2me | Definitions.Def_GevreyGibbsSep_bumpPotential
-- name    : GevreyGibbsSep_bumpPotential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:40:04.655963+00:00
-- url     : https://prove2.me/theorems/d460b0e8-fe51-479c-b30e-dbeed579b845
-- title:
--   Scaled potential $\beta E_{\nu,\ell,\alpha}=-\log\bar p_{\nu,\ell,\alpha}$
-- statement:
--   The scaled Gibbs potential of the bump,
--   $$\beta E_{\nu,\ell,\alpha}=-\log\bar p_{\nu,\ell,\alpha}=-F+\log Z_{\nu,\ell,\alpha},\qquad F=\log\big(1+(\alpha-1)\chi_{\nu,\ell}\big),$$
--   where $\bar p_{\nu,\ell,\alpha}$ is the periodic lift of the bump density.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (B71), p.45; Eq. (33), p.14

import Mathlib
import Definitions.Def_GevreyGibbsSep_bumpDensity

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The scaled Gibbs potential of the bump, `βE_{ν,ℓ,α} = −log p̄_{ν,ℓ,α}` (arXiv:2608.24527
(sha256 d4fd40eb…), Eq. (B71), p.45; (33), p.14). -/
noncomputable def bumpPotential {d : ℕ} (s ν ℓ α : ℝ) (x : Fin d → ℝ) : ℝ :=
  - Real.log (bumpDensity s ν ℓ α x)

end GevreyGibbsSep


