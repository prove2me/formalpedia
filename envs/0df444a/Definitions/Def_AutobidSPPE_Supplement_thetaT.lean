-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_thetaT
-- name    : AutobidSPPE_Supplement_thetaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:56:02.604891+00:00
-- url     : https://prove2.me/theorems/e7d065de-2af6-4c98-805a-0a1f87553882
-- title:
--   Throttling geometric factor $\theta=1-a\tau_{\min}/2$
-- statement:
--   $\theta=1-a\tau_{\min}/2$ with $a$ from (62) and $\tau_{\min}=\min_i\tau_i$ (Lemma 3.12). (It is not the pacing factor of Theorem 2.2.)
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 3.12, (79), p.36

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_aT
import Definitions.Def_AutobidSPPE_tauMin

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The throttling geometric factor `θ = 1 − aτ_min/2` of (79) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Lemma 3.12, (79), p.36), with
`a` from (62). (Not the SPPE `AutobidSPPE.theta`.) -/
noncomputable def thetaT {n : ℕ} (vhat : Fin n → ℝ) (m : ℝ) (τ : Fin n → ℝ) : ℝ :=
  1 - aT vhat m * tauMin τ / 2

end AutobidSPPE.Supplement


