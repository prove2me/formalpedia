-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_DT
-- name    : AutobidSPPE_Supplement_DT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:00:52.657347+00:00
-- url     : https://prove2.me/theorems/5f9edf84-6fb0-4e4b-994a-768d0cae0444
-- title:
--   $D=\max_i\log(1/\underline\alpha_i)$
-- statement:
--   $D=\max_i\log(1/\underline\alpha_i)$, the max-norm diameter of the log box $\prod_i[\log\underline\alpha_i,0]$ (Theorem 3.17).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.17, p.38

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_alphaLow

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `D = maxᵢ log(1/α̲ᵢ)` of Theorem 3.17, the max-norm diameter of the log box (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Theorem 3.17,
p.38), with `α̲` from (59).

**Formalization Note** `⨆ i` over `Fin n`, the maximum for `n ≥ 1`; `log` is the natural logarithm. -/
noncomputable def DT {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ := ⨆ i, Real.log (1 / alphaLow vhat ρ i)

end AutobidSPPE.Supplement


