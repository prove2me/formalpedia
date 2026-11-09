-- Prove2me | Definitions.Def_AutobidSPPE_Lp
-- name    : AutobidSPPE_Lp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:59:47.466415+00:00
-- url     : https://prove2.me/theorems/40b77105-6aae-491d-b44a-731936f0d207
-- title:
--   $L_p=2/\underline\gamma$
-- statement:
--   The uniform Lipschitz bound for conditional equilibria,
--   $$
--   L_p = 2/\underline\gamma .
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (11), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_gammaLow

namespace AutobidSPPE

/-- `L_p = 2/γ̲` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (11), p.11). -/
noncomputable def Lp {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ := 2 / gammaLow vhat ρ

end AutobidSPPE


