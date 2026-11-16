-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_gammaT
-- name    : AutobidSPPE_Supplement_gammaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:00:31.090467+00:00
-- url     : https://prove2.me/theorems/f8076a74-bfaf-48d1-9611-23f4523edbcf
-- title:
--   $\gamma=1-\sigma\min_i\tau_i(2\underline\alpha_i)$
-- statement:
--   $\gamma=1-\sigma\min_i\tau_i(2\underline\alpha_i)$, the contraction factor of the averaged iteration in log coordinates (Theorem 3.17).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.17, p.38

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_sigmaT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `γ = 1 − σ minᵢ τᵢ(2α̲ᵢ)` of Theorem 3.17 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Theorem 3.17, p.38), with `α̲` from (59). -/
noncomputable def gammaT {n : ℕ} (vbar vhat ρ τ : Fin n → ℝ) : ℝ :=
  1 - sigmaT vbar vhat ρ * ⨅ i, τ i * (2 * alphaLow vhat ρ i)

end AutobidSPPE.Supplement


