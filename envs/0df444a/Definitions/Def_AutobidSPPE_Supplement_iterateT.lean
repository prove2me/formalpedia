-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_iterateT
-- name    : AutobidSPPE_Supplement_iterateT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:42:14.373729+00:00
-- url     : https://prove2.me/theorems/a23a5283-3440-4252-b0df-d63569722d5b
-- title:
--   Simultaneous averaged throttling iteration (51)
-- statement:
--   From an initial profile $\alpha^{(0)}$ and fixed steps $\tau_i$, the **simultaneous averaged exact-response iteration** is
--   $$
--   \alpha^{(t+1)}_i=(1-\tau_i)\alpha^{(t)}_i+\tau_i\,r_i(\alpha^{(t)}_{-i}),
--   $$
--   every bidder responding to the same old profile.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (51), p.25; A3, p.28

import Mathlib
import Definitions.Def_AutobidSPPE_Supplement_responseT

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The simultaneous averaged exact-response iteration (51)
`α⁽ᵗ⁺¹⁾ᵢ = (1 − τᵢ)α⁽ᵗ⁾ᵢ + τᵢ rᵢ(α⁽ᵗ⁾₋ᵢ)` for throttling (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (51), p.25; A3, p.28): every bidder uses the
same old profile. -/
noncomputable def iterateT {n : ℕ} (vbar ρ : Fin n → ℝ) (tie : TieRule n) (τ α0 : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => α0
  | t + 1 => fun i => (1 - τ i) * iterateT vbar ρ tie τ α0 t i +
      τ i * responseT vbar ρ tie (iterateT vbar ρ tie τ α0 t) i

end AutobidSPPE.Supplement


