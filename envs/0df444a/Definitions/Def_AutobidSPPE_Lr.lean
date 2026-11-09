-- Prove2me | Definitions.Def_AutobidSPPE_Lr
-- name    : AutobidSPPE_Lr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:57:47.57405+00:00
-- url     : https://prove2.me/theorems/83044aa6-04a1-46f6-ac10-2d1ddb832d6e
-- title:
--   $L_r=\max\{1,U^2/\rho_{\min}^2\}$
-- statement:
--   The uniform Lipschitz bound for endpoint responses,
--   $$
--   L_r=\max\{1,\ U^2/\rho_{\min}^2\}.
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (11), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_supU
import Definitions.Def_AutobidSPPE_rhoMin

namespace AutobidSPPE

/-- `L_r = max{1, U²/ρ_min²}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (11), p.11). -/
noncomputable def Lr {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ :=
  max 1 (supU vhat ^ 2 / rhoMin ρ ^ 2)

end AutobidSPPE


