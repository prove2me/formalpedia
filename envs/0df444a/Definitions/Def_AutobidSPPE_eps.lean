-- Prove2me | Definitions.Def_AutobidSPPE_eps
-- name    : AutobidSPPE_eps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:03:02.728062+00:00
-- url     : https://prove2.me/theorems/e1d8e250-ebc5-4dac-9931-7cab5bd53330
-- title:
--   $\varepsilon=\min\{1/2,a/(4L_p(b_0+D_{\mathrm{tri}}))\}$
-- statement:
--   The auxiliary damping ratio
--   $$
--   \varepsilon=\min\Big\{\frac12,\ \frac{a}{4L_p(b_0+D_{\mathrm{tri}})}\Big\},\qquad a=\underline\gamma .
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (12), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_gammaLow
import Definitions.Def_AutobidSPPE_Lp
import Definitions.Def_AutobidSPPE_b0
import Definitions.Def_AutobidSPPE_Dtri

namespace AutobidSPPE

/-- `ε = min{1/2, a/(4L_p(b₀ + D_tri))}`, `a = γ̲` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (12), p.11). -/
noncomputable def eps {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ :=
  min (1 / 2) (gammaLow vhat ρ / (4 * Lp vhat ρ * (b0 vhat ρ + Dtri vhat ρ)))

end AutobidSPPE


