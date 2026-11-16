-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_lLow
-- name    : AutobidSPPE_Supplement_lLow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:46:09.092327+00:00
-- url     : https://prove2.me/theorems/8e954496-3c9a-4a18-8135-99841502da06
-- title:
--   $l=\min_i\underline\alpha_i$
-- statement:
--   $l=\min_i\underline\alpha_i$, the smallest lower box endpoint, used in the three-bidder certificate (61).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (59), p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_alphaLow

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- `l = minᵢ α̲ᵢ` of (59) (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (59), p.28).

**Formalization Note** `⨅ i` over `Fin n`, the minimum for `n ≥ 1`. -/
noncomputable def lLow {n : ℕ} (vhat ρ : Fin n → ℝ) : ℝ := ⨅ i, alphaLow vhat ρ i

end AutobidSPPE.Supplement


