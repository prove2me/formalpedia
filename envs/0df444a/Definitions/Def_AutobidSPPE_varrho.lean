-- Prove2me | Definitions.Def_AutobidSPPE_varrho
-- name    : AutobidSPPE_varrho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:51.258207+00:00
-- url     : https://prove2.me/theorems/2a3da88c-a6f5-4e26-a609-1eca9a41762f
-- title:
--   $\varrho=\min\{1/4,\rho_{\min}/(2U)\}$
-- statement:
--   The dimensionless constant
--   $$
--   \varrho = \min\Big\{\frac14,\ \frac{\rho_{\min}}{2U}\Big\}.
--   $$
--   It depends only on the budgets and the certified upper bounds $\hat v$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (10), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_supU
import Definitions.Def_AutobidSPPE_rhoMin

namespace AutobidSPPE

/-- `ϱ = min{1/4, ρ_min/(2U)}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (10), p.11). -/
noncomputable def varrho {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ :=
  min (1 / 4) (rhoMin ρ / (2 * supU vhat))

end AutobidSPPE


