-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_CresT
-- name    : AutobidSPPE_Supplement_CresT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:58:33.982867+00:00
-- url     : https://prove2.me/theorems/c1de0602-8db1-401d-966f-9abc37d7c3a6
-- title:
--   $C_{\mathrm{res}}=T_0+Q_{\mathrm{res}}^2/(1-\theta^2)$
-- statement:
--   $C_{\mathrm{res}}=T_0+Q_{\mathrm{res}}^2/(1-\theta^2)$ with $T_0=\lceil\log 2/\tau_{\min}\rceil$ (64), the bound on the sum of squared residuals in (82).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.14, (82), p.37

import Mathlib
import Definitions.Def_AutobidSPPE_T0
import Definitions.Def_AutobidSPPE_Supplement_QresT
import Definitions.Def_AutobidSPPE_Supplement_thetaT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `C_res = T₀ + Q_res²/(1 − θ²)` of (82) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Theorem 3.14, (82), p.37), with
`T₀ = ⌈log 2/τ_min⌉` (64). -/
noncomputable def CresT {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) (τ : Fin n → ℝ) : ℝ :=
  (T0 τ : ℝ) + QresT vhat ρ m ^ 2 / (1 - thetaT vhat m τ ^ 2)

end AutobidSPPE.Supplement


