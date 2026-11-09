-- Prove2me | Definitions.Def_AutobidSPPE_theta
-- name    : AutobidSPPE_theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:50.753048+00:00
-- url     : https://prove2.me/theorems/cb36bcf2-73ff-4e50-9dc3-644343d9b24a
-- title:
--   Geometric factor $\theta=1-a\tau_{\min}/2$
-- statement:
--   The geometric factor
--   $$
--   \theta = 1-\frac{a\,\tau_{\min}}{2},\qquad a=\underline\gamma .
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (15), p.12; Theorem 2.2, p.7

import Mathlib
import Definitions.Def_AutobidSPPE_gammaLow
import Definitions.Def_AutobidSPPE_tauMin

namespace AutobidSPPE

/-- The geometric factor `θ = 1 − aτ_min/2`, `a = γ̲` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (15), p.12; Theorem 2.2, p.7). -/
noncomputable def theta {n : ℕ} (vhat ρ τ : Fin n → ℝ) : ℝ :=
  1 - gammaLow vhat ρ * tauMin τ / 2

end AutobidSPPE


