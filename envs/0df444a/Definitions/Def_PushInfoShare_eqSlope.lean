-- Prove2me | Definitions.Def_PushInfoShare_eqSlope
-- name    : PushInfoShare_eqSlope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:33.888998+00:00
-- url     : https://prove2.me/theorems/771249bc-deae-430d-a962-238948fa6f16
-- title:
--   Equilibrium coefficient $B_i$ of Proposition 1
-- statement:
--   The coefficient of Proposition 1, for accuracies $s_i$ and weights $S_i$:
--   $$B_i=\frac{s_i\bigl(2(1+\phi)+\phi s_{3-i}\bigr)}{4(1+\phi)^2-\phi^2s_1s_2}+\frac{2(1+\phi)S_i\bar\delta_i+\phi s_iS_{3-i}\bar\delta_{3-i}}{4(1+\phi)^2-\phi^2s_1s_2}.$$
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), Proposition 1, p.11

import Mathlib
import Definitions.Def_PushInfoShare_shareBit

namespace PushInfoShare

/-- The coefficient `Bᵢ` of Proposition 1, Jain, SSRN:3388957 (PDF of 2021-04-25), p.11:
`Bᵢ = sᵢ(2(1+φ) + φs₃₋ᵢ)/(4(1+φ)² − φ²s₁s₂) + (2(1+φ)Sᵢδ̄ᵢ + φsᵢS₃₋ᵢδ̄₃₋ᵢ)/(4(1+φ)² − φ²s₁s₂)`.

**Formalization Note.** `s` and `S` are the accuracies and joint weights; `1 - i` is `3 − i`. -/
noncomputable def eqSlope (s S : Fin 2 → ℝ) (φ : ℝ) (δ : Fin 2 → Bool) (i : Fin 2) : ℝ :=
  s i * (2 * (1 + φ) + φ * s (1 - i)) / (4 * (1 + φ) ^ 2 - φ ^ 2 * s 0 * s 1) +
    (2 * (1 + φ) * S i * (1 - shareBit δ i) +
        φ * s i * S (1 - i) * (1 - shareBit δ (1 - i))) /
      (4 * (1 + φ) ^ 2 - φ ^ 2 * s 0 * s 1)

end PushInfoShare


