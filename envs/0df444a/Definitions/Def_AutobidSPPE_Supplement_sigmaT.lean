-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_sigmaT
-- name    : AutobidSPPE_Supplement_sigmaT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:59:06.473446+00:00
-- url     : https://prove2.me/theorems/e5e80495-6564-4c8c-b5c1-da3d3a3bcf32
-- title:
--   $\sigma$ of Theorem 3.17
-- statement:
--   $$
--   \sigma=\min_i\ \frac{4\Delta_i([n]\setminus\{i\})}{\bar v_i}\prod_{j\ne i}\underline\alpha_j ,
--   $$
--   with $\underline\alpha$ from (59).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Theorem 3.17, p.38

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_slackT
import Definitions.Def_AutobidSPPE_Supplement_alphaLow

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `σ = minᵢ (4Δᵢ([n]∖{i})/v̄ᵢ) ∏_{j≠i} α̲ⱼ` of Theorem 3.17 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Theorem 3.17, p.38), with
`α̲` from (59).

**Formalization Note** `⨅ i` over `Fin n`, the minimum for `n ≥ 1`. -/
noncomputable def sigmaT {n : ℕ} (vbar vhat ρ : Fin n → ℝ) : ℝ :=
  ⨅ i, 4 * slackT vbar i (Finset.univ.erase i) / vbar i * ∏ j ∈ Finset.univ.erase i, alphaLow vhat ρ j

end AutobidSPPE.Supplement


