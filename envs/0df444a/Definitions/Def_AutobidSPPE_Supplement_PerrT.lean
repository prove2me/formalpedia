-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_PerrT
-- name    : AutobidSPPE_Supplement_PerrT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:56:30.999991+00:00
-- url     : https://prove2.me/theorems/172b8a1b-6bed-4e4e-9b95-48499d8569be
-- title:
--   $P_{\mathrm{err}}=C_{\mathrm{tri}}W^{n-1}$
-- statement:
--   $P_{\mathrm{err}}=C_{\mathrm{tri}}W^{n-1}$, the prefactor of the distance bound (83).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (80), p.36

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_CtriT
import Definitions.Def_AutobidSPPE_Supplement_WT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `P_err = C_tri W^{n−1}` of (80) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (80), p.36). -/
noncomputable def PerrT {n : ℕ} (vhat ρ : Fin n → ℝ) (m : ℝ) : ℝ :=
  CtriT vhat m * WT vhat ρ m ^ (n - 1)

end AutobidSPPE.Supplement


