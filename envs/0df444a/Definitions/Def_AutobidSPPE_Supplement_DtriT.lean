-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_DtriT
-- name    : AutobidSPPE_Supplement_DtriT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:52:03.98739+00:00
-- url     : https://prove2.me/theorems/24f24f9e-39e6-45ea-83da-c47936749805
-- title:
--   $D_{\mathrm{tri}}=L_rC_{\mathrm{tri}}$
-- statement:
--   $D_{\mathrm{tri}}=L_r\,C_{\mathrm{tri}}$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (62), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_LrT
import Definitions.Def_AutobidSPPE_Supplement_CtriT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `D_tri = L_r C_tri` of (62) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (62), p.28). -/
noncomputable def DtriT {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) : ℝ := LrT vhat ρ * CtriT vhat m

end AutobidSPPE.Supplement


