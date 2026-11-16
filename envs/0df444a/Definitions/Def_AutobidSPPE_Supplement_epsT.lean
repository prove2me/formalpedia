-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_epsT
-- name    : AutobidSPPE_Supplement_epsT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:53:25.651628+00:00
-- url     : https://prove2.me/theorems/2e544542-0626-461f-83bc-3ae33de3de5d
-- title:
--   $\varepsilon=\min\{1/2,a/[4L_p(b_0+D_{\mathrm{tri}})]\}$
-- statement:
--   $\varepsilon=\min\{1/2,\ a/[4L_p(b_0+D_{\mathrm{tri}})]\}$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (62), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_aT
import Definitions.Def_AutobidSPPE_Supplement_LpT
import Definitions.Def_AutobidSPPE_Supplement_b0T
import Definitions.Def_AutobidSPPE_Supplement_DtriT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `ε = min{1/2, a/[4L_p(b₀ + D_tri)]}` of (62) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (62), p.28). -/
noncomputable def epsT {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) : ℝ :=
  min (1 / 2) (aT vhat m / (4 * LpT vhat m * (b0T vhat ρ m + DtriT vhat ρ m)))

end AutobidSPPE.Supplement


