-- Prove2me | Definitions.Def_AutobidSPPE_Ctri
-- name    : AutobidSPPE_Ctri
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:00:49.103273+00:00
-- url     : https://prove2.me/theorems/9f601cb4-b0cb-46f5-8d69-2c63d2b9919f
-- title:
--   $C_{\mathrm{tri}}=(1+L_p)^n$
-- statement:
--   The triangular inverse bound
--   $$
--   C_{\mathrm{tri}}=(1+L_p)^n .
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (12), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_Lp

namespace AutobidSPPE

/-- `C_tri = (1 + L_p)ⁿ` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (12), p.11). -/
noncomputable def Ctri {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ := (1 + Lp vhat ρ) ^ n

end AutobidSPPE


