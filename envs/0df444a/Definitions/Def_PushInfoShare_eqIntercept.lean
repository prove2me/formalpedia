-- Prove2me | Definitions.Def_PushInfoShare_eqIntercept
-- name    : PushInfoShare_eqIntercept
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:34.831578+00:00
-- url     : https://prove2.me/theorems/495a7f0b-31f2-48e6-bc71-7cc977657a29
-- title:
--   Constant term of the equilibrium price in Proposition 1
-- statement:
--   The constant term of the equilibrium price $w_i$ of Proposition 1:
--   $$\frac{\bigl(2+3\phi-\tfrac{S_{3-i}}{B_{3-i}}\bar\delta_{3-i}\bigr)a}{\bigl(2(1+\phi)-\tfrac{S_i}{B_i}\bar\delta_i\bigr)\bigl(2(1+\phi)-\tfrac{S_{3-i}}{B_{3-i}}\bar\delta_{3-i}\bigr)-\phi^2},$$
--   with $B_i$ the equilibrium coefficient.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 1, p.11

import Mathlib
import Definitions.Def_PushInfoShare_eqSlope

namespace PushInfoShare

/-- The constant term of the equilibrium price `wᵢ` in Proposition 1, Jain, SSRN:3388957 (PDF of
2021-04-25), p.11:
`(2 + 3φ − (S₃₋ᵢ/B₃₋ᵢ)δ̄₃₋ᵢ) a / ((2(1+φ) − (Sᵢ/Bᵢ)δ̄ᵢ)(2(1+φ) − (S₃₋ᵢ/B₃₋ᵢ)δ̄₃₋ᵢ) − φ²)`,
with `B` given by `eqSlope`. -/
noncomputable def eqIntercept (s S : Fin 2 → ℝ) (a φ : ℝ) (δ : Fin 2 → Bool) (i : Fin 2) : ℝ :=
  (2 + 3 * φ - S (1 - i) / eqSlope s S φ δ (1 - i) * (1 - shareBit δ (1 - i))) * a /
    ((2 * (1 + φ) - S i / eqSlope s S φ δ i * (1 - shareBit δ i)) *
        (2 * (1 + φ) - S (1 - i) / eqSlope s S φ δ (1 - i) * (1 - shareBit δ (1 - i))) -
      φ ^ 2)

end PushInfoShare


