-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_QresT
-- name    : AutobidSPPE_Supplement_QresT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:57:21.982858+00:00
-- url     : https://prove2.me/theorems/690b1cba-6bd8-4ebf-bed7-e973e57cbbbc
-- title:
--   $Q_{\mathrm{res}}=(1+L_r)P_{\mathrm{err}}$
-- statement:
--   $Q_{\mathrm{res}}=(1+L_r)P_{\mathrm{err}}$, the prefactor of the residual bound (83).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (80), p.36

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_LrT
import Definitions.Def_AutobidSPPE_Supplement_PerrT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `Q_res = (1 + L_r) P_err` of (80) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (80), p.36). -/
noncomputable def QresT {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) : ℝ := (1 + LrT vhat ρ) * PerrT vhat ρ m

end AutobidSPPE.Supplement


