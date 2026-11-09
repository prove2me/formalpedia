-- Prove2me | Definitions.Def_AutobidSPPE_residual
-- name    : AutobidSPPE_residual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:02:52.379287+00:00
-- url     : https://prove2.me/theorems/13bd4c48-0422-41ec-bd35-8d9f4247e0bf
-- title:
--   Response residual $\mathcal R(\alpha)=\alpha-r(\alpha)$
-- statement:
--   The **response residual** is the vector
--   $$
--   \mathcal R(\alpha) = \alpha - r(\alpha), \qquad \mathcal R_i(\alpha)=\alpha_i - r_i(\alpha_{-i}).
--   $$
--   Its fixed points $\mathcal R(\alpha)=0$ are the fixed points of the response map.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (5), p.10

import Mathlib
import Definitions.Def_AutobidSPPE_response

namespace AutobidSPPE

/-- The response residual `R(α) = α − r(α)`, `Rᵢ(α) = αᵢ − rᵢ(α₋ᵢ)` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (5), p.10). -/
noncomputable def residual {n : ℕ} (vbar ρ : Fin n → ℝ) (tie : TieRule n) (α : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => α i - response vbar ρ tie α i

end AutobidSPPE


