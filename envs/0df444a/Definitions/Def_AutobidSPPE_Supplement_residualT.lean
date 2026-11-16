-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_residualT
-- name    : AutobidSPPE_Supplement_residualT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:41:42.10712+00:00
-- url     : https://prove2.me/theorems/a4d2d7dd-542d-43f3-bdf7-a0e1c41b4dba
-- title:
--   Throttling response residual $\mathcal R(\alpha)=\alpha-r(\alpha)$
-- statement:
--   The **response residual** is $\mathcal R(\alpha)=\alpha-r(\alpha)$, coordinatewise $\mathcal R_i(\alpha)=\alpha_i-r_i(\alpha_{-i})$. Its zeros are the fixed points of the response.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §3.1, p.25

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_responseT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The throttling response residual `R(α) = α − r(α)` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §3.1, p.25). -/
noncomputable def residualT {n : ℕ} (vbar ρ : Fin n → ℝ) (tie : TieRule n) (α : Fin n → ℝ) :
    Fin n → ℝ :=
  fun i => α i - responseT vbar ρ tie α i

end AutobidSPPE.Supplement


