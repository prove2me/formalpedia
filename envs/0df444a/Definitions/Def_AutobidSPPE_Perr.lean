-- Prove2me | Definitions.Def_AutobidSPPE_Perr
-- name    : AutobidSPPE_Perr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:04:29.324256+00:00
-- url     : https://prove2.me/theorems/03c89d46-bd71-4ab7-9326-43991c8d6b7e
-- title:
--   $P_{\mathrm{err}}=\max\{1,C_{\mathrm{tri}}W^{n-1}U/(4\rho_{\min})\}$
-- statement:
--   The multiplier-distance prefactor
--   $$
--   P_{\mathrm{err}}=\max\Big\{1,\ \frac{C_{\mathrm{tri}}W^{n-1}U}{4\rho_{\min}}\Big\}.
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (16), p.12; (48), p.24

import Mathlib
import Definitions.Def_AutobidSPPE_Ctri
import Definitions.Def_AutobidSPPE_W
import Definitions.Def_AutobidSPPE_supU
import Definitions.Def_AutobidSPPE_rhoMin

namespace AutobidSPPE

/-- `P_err = max{1, C_tri W^{n−1} U/(4ρ_min)}` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (16), p.12; (48), p.24). -/
noncomputable def Perr {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ :=
  max 1 (Ctri vhat ρ * W vhat ρ ^ (n - 1) * supU vhat / (4 * rhoMin ρ))

end AutobidSPPE


