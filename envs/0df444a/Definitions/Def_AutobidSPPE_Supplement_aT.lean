-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_aT
-- name    : AutobidSPPE_Supplement_aT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:49:59.359205+00:00
-- url     : https://prove2.me/theorems/28fe1d44-b3d0-4339-be10-96a0dd56fb01
-- title:
--   Sector lower bound $a=m/(n!H^n)$
-- statement:
--   $a=m/(n!\,H^n)$, the lower sector bound of the reduced scalar residuals (Lemma 3.10).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (62), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_HT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The sector lower bound `a = m/(n! Hⁿ)` of (62) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (62), p.28). -/
noncomputable def aT {n : ℕ} (vhat : Fin n → ℝ) (m : ℝ) : ℝ :=
  m / ((Nat.factorial n : ℝ) * HT vhat ^ n)

end AutobidSPPE.Supplement


