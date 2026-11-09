-- Prove2me | Definitions.Def_AutobidSPPE_Dtri
-- name    : AutobidSPPE_Dtri
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:02:00.892877+00:00
-- url     : https://prove2.me/theorems/e6bdf5a3-770b-4d1c-b84d-4fa9dcb37ef0
-- title:
--   $D_{\mathrm{tri}}=L_rC_{\mathrm{tri}}$
-- statement:
--   The induced response-error bound
--   $$
--   D_{\mathrm{tri}}=L_r\,C_{\mathrm{tri}} .
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (12), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_Lr
import Definitions.Def_AutobidSPPE_Ctri

namespace AutobidSPPE

/-- `D_tri = L_r C_tri` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (12), p.11). -/
noncomputable def Dtri {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ := Lr vhat ρ * Ctri vhat ρ

end AutobidSPPE


