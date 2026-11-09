-- Prove2me | Definitions.Def_AutobidSPPE_iterate
-- name    : AutobidSPPE_iterate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:03:04.846292+00:00
-- url     : https://prove2.me/theorems/802072db-e983-4b63-b444-64a82210226c
-- title:
--   Simultaneous damped best-response dynamics (Definition 1.1)
-- statement:
--   Given an initial profile $\alpha^{(0)}$ and damping steps $\tau_1,\dots,\tau_n$, the **simultaneous damped best-response dynamics** is
--   $$
--   \alpha^{(t+1)}_i = (1-\tau_i)\,\alpha^{(t)}_i + \tau_i\, r_i\big(\alpha^{(t)}_{-i}\big),\qquad i\in[n],
--   $$
--   where every bidder uses the exact response to the same current profile $\alpha^{(t)}$ (Assumption 2.4).
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Definition 1.1, p.5; Assumption 2.4, p.11

import Mathlib
import Definitions.Def_AutobidSPPE_response

namespace AutobidSPPE

/-- The simultaneous damped best-response dynamics (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Definition 1.1, p.5; Assumption 2.4,
p.11): `α⁽ᵗ⁺¹⁾ᵢ = (1 − τᵢ)α⁽ᵗ⁾ᵢ + τᵢ rᵢ(α⁽ᵗ⁾₋ᵢ)`, every bidder using the same current profile. -/
noncomputable def iterate {n : ℕ} (vbar ρ : Fin n → ℝ) (tie : TieRule n) (τ α0 : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => α0
  | t + 1 => fun i => (1 - τ i) * iterate vbar ρ tie τ α0 t i +
      τ i * response vbar ρ tie (iterate vbar ρ tie τ α0 t) i

end AutobidSPPE


