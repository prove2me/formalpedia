-- Prove2me | Definitions.Def_AutobidSPPE_Qres
-- name    : AutobidSPPE_Qres
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:04:20.269182+00:00
-- url     : https://prove2.me/theorems/9ce192ad-3215-4d6c-9d9e-b9e2392d5310
-- title:
--   $Q_{\mathrm{res}}=\max\{1,(1+L_r)C_{\mathrm{tri}}W^{n-1}U/(4\rho_{\min})\}$
-- statement:
--   The response-residual prefactor
--   $$
--   Q_{\mathrm{res}}=\max\Big\{1,\ \frac{(1+L_r)\,C_{\mathrm{tri}}W^{n-1}U}{4\rho_{\min}}\Big\}.
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (16), p.12; (45), p.23

import Mathlib
import Definitions.Def_AutobidSPPE_Lr
import Definitions.Def_AutobidSPPE_Ctri
import Definitions.Def_AutobidSPPE_W
import Definitions.Def_AutobidSPPE_supU
import Definitions.Def_AutobidSPPE_rhoMin

namespace AutobidSPPE

/-- `Q_res = max{1, (1 + L_r)C_tri W^{n−1} U/(4ρ_min)}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (16), p.12; (45), p.23). -/
noncomputable def Qres {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ :=
  max 1 ((1 + Lr vhat ρ) * Ctri vhat ρ * W vhat ρ ^ (n - 1) * supU vhat / (4 * rhoMin ρ))

end AutobidSPPE


