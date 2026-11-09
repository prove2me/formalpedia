-- Prove2me | Definitions.Def_AutobidSPPE_W
-- name    : AutobidSPPE_W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:02:47.96189+00:00
-- url     : https://prove2.me/theorems/7f9af78b-0674-4c80-b233-d79a66e03fc9
-- title:
--   Error-weight ratio $W=\max\{2,4D_{\mathrm{tri}}/a\}$
-- statement:
--   The error-weight ratio
--   $$
--   W=\max\{2,\ 4D_{\mathrm{tri}}/a\},\qquad a=\underline\gamma .
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (12), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_Dtri
import Definitions.Def_AutobidSPPE_gammaLow

namespace AutobidSPPE

/-- The error-weight ratio `W = max{2, 4D_tri/a}`, `a = γ̲` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (12), p.11). -/
noncomputable def W {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ :=
  max 2 (4 * Dtri vhat ρ / gammaLow vhat ρ)

end AutobidSPPE


