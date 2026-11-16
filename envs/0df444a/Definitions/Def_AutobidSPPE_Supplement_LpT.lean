-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_LpT
-- name    : AutobidSPPE_Supplement_LpT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:49:18.969203+00:00
-- url     : https://prove2.me/theorems/2ed790b6-924e-478c-a36f-e87a5a6a1ed6
-- title:
--   Prefix Lipschitz constant $L_p=\max\{1,n!H^{n-1}C/m\}$
-- statement:
--   $L_p=\max\{1,\ n!\,H^{n-1}C/m\}$, the Lipschitz bound of the conditional prefix equilibria, for a certificate value $m$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (62), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_HT
import Definitions.Def_AutobidSPPE_Supplement_CT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The prefix Lipschitz constant `L_p = max{1, n! H^{n−1} C/m}` of (62) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (62), p.28),
for a certificate value `m`. -/
noncomputable def LpT {n : ℕ} (vhat : Fin n → ℝ) (m : ℝ) : ℝ :=
  max 1 ((Nat.factorial n : ℝ) * HT vhat ^ (n - 1) * CT vhat / m)

end AutobidSPPE.Supplement


