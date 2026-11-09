-- Prove2me | Definitions.Def_AutobidSPPE_endpointIterate
-- name    : AutobidSPPE_endpointIterate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:02:54.286202+00:00
-- url     : https://prove2.me/theorems/9ecc59bb-9403-476f-9813-2544bb26ac4e
-- title:
--   Endpoint damped dynamics (8)
-- statement:
--   In endpoint coordinates the damped dynamics reads
--   $$
--   y^{(t+1)}_i=(1-\tau_i)\,y^{(t)}_i+\tau_i\,\mathsf b_i\big(y^{(t)}_{-i}\big),
--   $$
--   all bidders updating from the same current endpoint profile.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (8), p.10

import Mathlib
import Definitions.Def_AutobidSPPE_endpointResponse

namespace AutobidSPPE

/-- The endpoint version of the damped dynamics (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (8), p.10):
`y⁽ᵗ⁺¹⁾ᵢ = (1 − τᵢ)y⁽ᵗ⁾ᵢ + τᵢ𝖻ᵢ(y⁽ᵗ⁾₋ᵢ)`. -/
noncomputable def endpointIterate {n : ℕ} (vbar ρ τ y0 : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => y0
  | t + 1 => fun i => (1 - τ i) * endpointIterate vbar ρ τ y0 t i +
      τ i * endpointResponse vbar ρ (endpointIterate vbar ρ τ y0 t) i

end AutobidSPPE


