-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_HT
-- name    : AutobidSPPE_Supplement_HT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:46:56.295172+00:00
-- url     : https://prove2.me/theorems/d8cb0b1a-2831-49ce-a9e4-322390ab8a54
-- title:
--   $H=\max\{1,U/4\}$
-- statement:
--   $H=\max\{1,U/4\}$ with $U=\max_i\hat v_i$; it bounds the entries of the spending Jacobian.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (59), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_supU

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `H = max{1, U/4}` of (59) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (59), p.28), a bound on the entries of `Js`. -/
noncomputable def HT {n : ℕ} (vhat : Fin n → ℝ) : ℝ := max 1 (supU vhat / 4)

end AutobidSPPE.Supplement


