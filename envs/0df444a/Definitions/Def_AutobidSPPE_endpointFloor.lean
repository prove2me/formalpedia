-- Prove2me | Definitions.Def_AutobidSPPE_endpointFloor
-- name    : AutobidSPPE_endpointFloor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:56.670471+00:00
-- url     : https://prove2.me/theorems/533f7ae4-34ba-4108-b99c-a953db2ca28a
-- title:
--   Endpoint floor $\underline y_i=\min\{\bar v_i/2,2\rho_i\}$
-- statement:
--   The **endpoint floor** of bidder $i$ is
--   $$
--   \underline y_i = \min\{\bar v_i/2,\ 2\rho_i\}.
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (9), p.10

import Mathlib

namespace AutobidSPPE

/-- The endpoint floor `y̲ᵢ = min{v̄ᵢ/2, 2ρᵢ}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (9), p.10). -/
noncomputable def endpointFloor {n : ℕ} (vbar ρ : Fin n → ℝ) (i : Fin n) : ℝ :=
  min (vbar i / 2) (2 * ρ i)

end AutobidSPPE


