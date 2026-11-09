-- Prove2me | Definitions.Def_AutobidSPPE_endpointResidual
-- name    : AutobidSPPE_endpointResidual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:02:21.710451+00:00
-- url     : https://prove2.me/theorems/8988d4c5-4eab-46e7-afcf-a0d4b9d68140
-- title:
--   Endpoint response residual $\mathcal G_i(y)=y_i-\mathsf b_i(y_{-i})$
-- statement:
--   The **endpoint response residual** of bidder $i$ is
--   $$
--   \mathcal G_i(y)=y_i-\mathsf b_i(y_{-i}).
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §2.8, p.22

import Mathlib
import Definitions.Def_AutobidSPPE_endpointResponse

namespace AutobidSPPE

/-- The endpoint response residual `𝒢ᵢ(y) = yᵢ − 𝖻ᵢ(y₋ᵢ)` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §2.8, p.22). -/
noncomputable def endpointResidual {n : ℕ} (vbar ρ y : Fin n → ℝ) (i : Fin n) : ℝ :=
  y i - endpointResponse vbar ρ y i

end AutobidSPPE


