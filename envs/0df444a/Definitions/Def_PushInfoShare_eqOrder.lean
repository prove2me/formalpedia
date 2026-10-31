-- Prove2me | Definitions.Def_PushInfoShare_eqOrder
-- name    : PushInfoShare_eqOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:47.852272+00:00
-- url     : https://prove2.me/theorems/e834232f-843b-42a1-abc2-dad6d25b2acf
-- title:
--   Equilibrium order rule of Proposition 1 (corrected)
-- statement:
--   With $r_j=(S_j/B_j)\bar\delta_j$, the equilibrium order rule is
--   $$q_i=\tfrac12\bigl(a-(1+\phi)w_i+\phi w_{3-i}+S_1\delta_1Y_1+S_2\delta_2Y_2\bigr)+\tfrac12\Bigl(r_1w_1+r_2w_2-\frac{\bigl((2+3\phi)(r_1+r_2)-2r_1r_2\bigr)a}{(2(1+\phi)-r_1)(2(1+\phi)-r_2)-\phi^2}\Bigr).$$
--
--   **Formalization Note** The page prints $S_2\delta_1Y_2$ for $S_2\delta_2Y_2$, and $(S_1/B_1)\bar\delta_1+(S_1/B_1)\bar\delta_1$ for $r_1+r_2$. The retailer's first-order condition gives the form used here.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 1, p.11 (two index slips corrected)

import Mathlib
import Definitions.Def_PushInfoShare_eqSlope

namespace PushInfoShare

/-- The equilibrium order rule `qᵢ` of Proposition 1, Jain, SSRN:3388957 (PDF of 2021-04-25), p.11,
with its two index slips corrected: with `rⱼ = (Sⱼ/Bⱼ)δ̄ⱼ`,
`qᵢ = ½(a − (1+φ)wᵢ + φw₃₋ᵢ + S₁δ₁Y₁ + S₂δ₂Y₂)`
`  + ½(r₁w₁ + r₂w₂ − ((2+3φ)(r₁ + r₂) − 2r₁r₂) a / ((2(1+φ) − r₁)(2(1+φ) − r₂) − φ²))`.

**Formalization Note.** The page prints `S₂δ₁Y₂` for `S₂δ₂Y₂` and `(S₁/B₁)δ̄₁ + (S₁/B₁)δ̄₁` for
`(S₁/B₁)δ̄₁ + (S₂/B₂)δ̄₂`. The manufacturers are `0, 1` here. -/
noncomputable def eqOrder (s S : Fin 2 → ℝ) (a φ : ℝ) (δ : Fin 2 → Bool) (i : Fin 2)
    (w y : Fin 2 → ℝ) : ℝ :=
  let r : Fin 2 → ℝ := fun j => S j / eqSlope s S φ δ j * (1 - shareBit δ j)
  1 / 2 * (a - (1 + φ) * w i + φ * w (1 - i) +
      S 0 * shareBit δ 0 * y 0 + S 1 * shareBit δ 1 * y 1) +
    1 / 2 * (r 0 * w 0 + r 1 * w 1 -
      ((2 + 3 * φ) * (r 0 + r 1) - 2 * (r 0 * r 1)) * a /
        ((2 * (1 + φ) - r 0) * (2 * (1 + φ) - r 1) - φ ^ 2))

end PushInfoShare


