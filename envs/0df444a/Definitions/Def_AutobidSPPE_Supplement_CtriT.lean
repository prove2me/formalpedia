-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_CtriT
-- name    : AutobidSPPE_Supplement_CtriT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:51:19.633196+00:00
-- url     : https://prove2.me/theorems/2cdf2f3b-22f0-4c24-84f3-914fa8c87e43
-- title:
--   $C_{\mathrm{tri}}=(1+L_p)^n$
-- statement:
--   $C_{\mathrm{tri}}=(1+L_p)^n$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (62), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_LpT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `C_tri = (1 + L_p)ⁿ` of (62) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (62), p.28). -/
noncomputable def CtriT {n : ℕ} (vhat : Fin n → ℝ) (m : ℝ) : ℝ := (1 + LpT vhat m) ^ n

end AutobidSPPE.Supplement


