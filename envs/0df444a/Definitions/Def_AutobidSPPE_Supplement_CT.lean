-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_CT
-- name    : AutobidSPPE_Supplement_CT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:47:20.889193+00:00
-- url     : https://prove2.me/theorems/69535816-481d-43fd-925f-2888b1374609
-- title:
--   $C=\max\{1,nU/4\}$
-- statement:
--   $C=\max\{1,nU/4\}$ with $U=\max_i\hat v_i$; it bounds the row-sum norm of the spending Jacobian.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (59), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_supU

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `C = max{1, nU/4}` of (59) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (59), p.28), a bound on the row-sum norm of `Js`. -/
noncomputable def CT {n : ℕ} (vhat : Fin n → ℝ) : ℝ := max 1 ((n : ℝ) * supU vhat / 4)

end AutobidSPPE.Supplement


