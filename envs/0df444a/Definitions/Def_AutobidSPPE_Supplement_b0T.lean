-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_b0T
-- name    : AutobidSPPE_Supplement_b0T
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:50:44.200627+00:00
-- url     : https://prove2.me/theorems/cbe208a4-1a22-4757-a47a-6183b31fb4dd
-- title:
--   $b_0=1+L_rL_p$
-- statement:
--   $b_0=1+L_rL_p$, the upper sector bound; the first step satisfies $\tau_1\le b_0^{-1}$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (62), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_LrT
import Definitions.Def_AutobidSPPE_Supplement_LpT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `b₀ = 1 + L_r L_p` of (62) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (62), p.28). -/
noncomputable def b0T {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) : ℝ := 1 + LrT vhat ρ * LpT vhat m

end AutobidSPPE.Supplement


