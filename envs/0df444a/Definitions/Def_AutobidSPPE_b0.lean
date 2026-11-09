-- Prove2me | Definitions.Def_AutobidSPPE_b0
-- name    : AutobidSPPE_b0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:00:46.521199+00:00
-- url     : https://prove2.me/theorems/c855b184-3677-407d-868d-abdc3f2be64a
-- title:
--   $b_0=1+L_rL_p$
-- statement:
--   The upper bound on the reduced scalar residual ratio,
--   $$
--   b_0 = 1+L_rL_p .
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (12), p.11

import Mathlib
import Definitions.Def_AutobidSPPE_Lr
import Definitions.Def_AutobidSPPE_Lp

namespace AutobidSPPE

/-- `b₀ = 1 + L_r L_p` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (12), p.11). -/
noncomputable def b0 {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ := 1 + Lr vhat ρ * Lp vhat ρ

end AutobidSPPE


