-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_WT
-- name    : AutobidSPPE_Supplement_WT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:52:55.057706+00:00
-- url     : https://prove2.me/theorems/bb4c6cbd-c2de-4b32-9464-e13fe01b3f4c
-- title:
--   $W=\max\{2,4D_{\mathrm{tri}}/a\}$
-- statement:
--   $W=\max\{2,\ 4D_{\mathrm{tri}}/a\}$, the ratio of consecutive triangular error weights $w_i=W^{i-1}$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (62), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_DtriT
import Definitions.Def_AutobidSPPE_Supplement_aT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `W = max{2, 4D_tri/a}` of (62) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (62), p.28). -/
noncomputable def WT {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) : ℝ := max 2 (4 * DtriT vhat ρ m / aT vhat m)

end AutobidSPPE.Supplement


