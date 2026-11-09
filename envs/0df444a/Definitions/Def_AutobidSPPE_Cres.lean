-- Prove2me | Definitions.Def_AutobidSPPE_Cres
-- name    : AutobidSPPE_Cres
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:06:27.59056+00:00
-- url     : https://prove2.me/theorems/961c5757-d251-4324-a015-c1b889165c1a
-- title:
--   $C_{\mathrm{res}}=T_0+Q_{\mathrm{res}}^2/(1-\theta^2)$
-- statement:
--   The squared-residual summability constant
--   $$
--   C_{\mathrm{res}} = T_0 + \frac{Q_{\mathrm{res}}^2}{1-\theta^2}.
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (16), p.12; (47), p.23

import Mathlib
import Definitions.Def_AutobidSPPE_T0
import Definitions.Def_AutobidSPPE_Qres
import Definitions.Def_AutobidSPPE_theta

namespace AutobidSPPE

/-- `C_res = T₀ + Q_res²/(1 − θ²)` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (16), p.12; (47), p.23). -/
noncomputable def Cres {n : ℕ} (vhat ρ τ : Fin n → ℝ) : ℝ :=
  (T0 τ : ℝ) + Qres vhat ρ ^ 2 / (1 - theta vhat ρ τ ^ 2)

end AutobidSPPE


