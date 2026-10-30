-- Prove2me | Definitions.Def_DigitalPrivacy_DataStrategy_cStar
-- name    : DigitalPrivacy_DataStrategy_cStar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:08:23.904609+00:00
-- url     : https://prove2.me/theorems/5f784167-2b6f-4284-9472-a942e11ee153
-- title:
--   Optimal data protection $C^\star$, display (6)
-- statement:
--   With $\xi^\star$ from (5), define
--
--   $$C^\star=\frac{\xi^\star}{1-\beta}\Big(-\xi^\star+\sqrt{\tfrac1\psi(1+\rho\xi^\star)(1-P(1-\xi^\star))}\Big).$$
--
--   This equals $C_h(\xi^\star)$ of Lemma 1.
--
--   **Formalization Note** Literal; meant for $\psi>0$.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Theorem 1, display (6), p. 11 (PDF 12)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_xiStar

namespace DigitalPrivacy.DataStrategy

/-- **The optimal data protection `C*`, display (6).**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Theorem 1, display (6), p. 11 (PDF 12): "C⋆ = ξ⋆/(1 − β) · (−ξ⋆ + √((1/ψ)(1 + ρξ⋆)(1 −
P(1 − ξ⋆))))", with `ξ⋆ = xiStar ρ P ψ` of display (5).

**Formalization Note.** The formula is literal; it equals `C_h(ξ*)` of Lemma 1 (proved in
`Solutions/verification/DigitalPrivacy_DataStrategy_sanity.lean`). Meant for `ψ > 0`. -/
noncomputable def cStar (β ρ P ψ : ℝ) : ℝ :=
  xiStar ρ P ψ / (1 - β) *
    (-xiStar ρ P ψ + Real.sqrt ((1 / ψ) * (1 + ρ * xiStar ρ P ψ) * (1 - P * (1 - xiStar ρ P ψ))))

end DigitalPrivacy.DataStrategy


