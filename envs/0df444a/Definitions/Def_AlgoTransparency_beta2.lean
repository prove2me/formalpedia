-- Prove2me | Definitions.Def_AlgoTransparency_beta2
-- name    : AlgoTransparency_beta2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:49:39.038989+00:00
-- url     : https://prove2.me/theorems/efef6d3b-3761-49c0-8052-602fb029f045
-- title:
--   Threshold $\beta_2$ of eq. (14)
-- statement:
--   The threshold
--
--   $$
--   \beta_2=R-\frac{\alpha R(1-\lambda)}{(\alpha-R)\lambda+R(1-\lambda)} .
--   $$
--
--   In region $C_2$ the firm prefers the transparent algorithm exactly when $\beta>\beta_2$.
--
--   **Formalization Note** The denominator is positive under the standing assumptions.
-- source:
--   Wang, Huang, Jasin & Singh, Algorithmic Transparency with Strategic Users, arXiv:2008.09283v1, eq. (14), p.23 (PDF 24)

import Mathlib
import Definitions.Def_AlgoTransparency_Params

namespace AlgoTransparency

/-- **The threshold `β2`** of Wang, Huang, Jasin & Singh, arXiv:2008.09283v1, eq. (14), p.23
(PDF 24): `β2 = R − αR(1 − λ)/((α − R)λ + R(1 − λ))`. In region C2 the firm prefers transparency
iff `β > β2`.

**Formalization Note.** Under the standing assumptions (`α > R > 0`, `λ ∈ (1/2, 1]`) the
denominator `(α − R)λ + R(1 − λ)` is positive, so `/` takes its mathematical value. -/
noncomputable def beta2 (p : Params) : ℝ :=
  p.R - p.α * p.R * (1 - p.lam) / ((p.α - p.R) * p.lam + p.R * (1 - p.lam))

end AlgoTransparency


