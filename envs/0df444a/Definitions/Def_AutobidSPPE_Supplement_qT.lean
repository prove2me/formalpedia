-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_qT
-- name    : AutobidSPPE_Supplement_qT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:59:52.296148+00:00
-- url     : https://prove2.me/theorems/9ccec70c-a582-4f9e-8a86-0dd52eb4f23e
-- title:
--   $q=1-\sigma$
-- statement:
--   $q=1-\sigma$, the max-norm Lipschitz constant of the log response in Theorem 3.17.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.17, p.38

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_sigmaT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `q = 1 − σ` of Theorem 3.17 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Theorem 3.17, p.38). -/
noncomputable def qT {n : ℕ} (vbar vhat ρ : Fin n → ℝ) : ℝ := 1 - sigmaT vbar vhat ρ

end AutobidSPPE.Supplement


