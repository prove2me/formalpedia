-- Prove2me | Definitions.Def_AutobidSPPE_endpointBox
-- name    : AutobidSPPE_endpointBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:19.226929+00:00
-- url     : https://prove2.me/theorems/e16792cd-b028-42b5-b36f-a8ad3812cded
-- title:
--   Positive endpoint box $\mathcal Y=\prod_i[\underline y_i,\bar v_i]$
-- statement:
--   The **positive endpoint box** is the rectangle
--   $$
--   \mathcal Y=\prod_{i=1}^n[\underline y_i,\bar v_i]\subset\mathbb R^n .
--   $$
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (9), p.10

import Mathlib
import Definitions.Def_AutobidSPPE_endpointFloor

namespace AutobidSPPE

/-- The positive endpoint box `𝒴 = ∏ᵢ [y̲ᵢ, v̄ᵢ]` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (9), p.10). -/
def endpointBox {n : ℕ} (vbar ρ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | ∀ i, endpointFloor vbar ρ i ≤ y i ∧ y i ≤ vbar i}

end AutobidSPPE


