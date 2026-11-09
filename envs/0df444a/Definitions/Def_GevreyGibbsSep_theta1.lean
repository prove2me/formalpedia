-- Prove2me | Definitions.Def_GevreyGibbsSep_theta1
-- name    : GevreyGibbsSep_theta1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:39.937031+00:00
-- url     : https://prove2.me/theorems/86c669db-54bb-4e40-86e9-9557c73fc482
-- title:
--   Mollified step $\theta_1$
-- statement:
--   The **mollified step** is
--   $$\theta_1(x)=\frac{1}{Z_s}\int_{-1}^{x}\psi_s(y)\,dy,\qquad Z_s=\int_{-1}^{1}\psi_s(y)\,dy .$$
--   It rises smoothly from $0$ (for $x\le-1$) to $1$ (for $x\ge1$).
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Definition B.5, Eq. (B16), p.37

import Mathlib
import Definitions.Def_GevreyGibbsSep_psiS

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The mollified step `θ₁(x) = (∫_{−1}^x ψ_s)/Z_s`, `Z_s = ∫_{−1}^1 ψ_s` (arXiv:2608.24527
(sha256 d4fd40eb…), Definition B.5, Eq. (B16), p.37). -/
noncomputable def theta1 (s x : ℝ) : ℝ :=
  (∫ y in (-1 : ℝ)..x, psiS s y) / (∫ y in (-1 : ℝ)..1, psiS s y)

end GevreyGibbsSep


