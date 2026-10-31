-- Prove2me | Definitions.Def_DuanCV_Gauss_eprV
-- name    : DuanCV_Gauss_eprV
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:26.676107+00:00
-- url     : https://prove2.me/theorems/579faf73-7432-40a6-8bea-f8cf241948ca
-- title:
--   The EPR-type operator $|a|\hat p_1+(\varepsilon/a)\hat p_2$
-- statement:
--   For real $a\neq0$ and a real $\varepsilon$, this is the coefficient vector on $(\hat x_1,\hat p_1,\hat x_2,\hat p_2)$ of
--
--   $$\hat v=|a|\,\hat p_1+\frac{\varepsilon}{a}\,\hat p_2 .$$
--
--   With $\varepsilon=-1$ it is Eq. (2b). With $a=a_0>0$ and $\varepsilon=-c_2/|c_2|$ it is Eq. (15b).
--
--   **Formalization Note** The sign is a parameter, so that no quotient $c/|c|$ appears in Lean.
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eq. (2b), p. 1, and Eq. (15b), p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace DuanCV.Gauss

/-- **The momentum-type EPR operator `|a| p̂₁ + (ε/a) p̂₂`, as a coefficient vector.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Eq. (2b), p. 1 and Eq. (15b), p. 4.

Coefficients on `(x̂₁, p̂₁, x̂₂, p̂₂)`, indexed by `QuadratureIndex 2`. Eq. (2b) is `eprV a (-1)`.
Eq. (15b) is `eprV a₀ (-ε₂)` with `a₀ > 0` and `ε₂ = c₂/|c₂|`.

**Formalization Note.** The sign is a real parameter `ε`, so that no Lean division `c/|c|` occurs. -/
noncomputable def eprV (a ε : ℝ) : QuadratureIndex 2 → ℝ := fun k =>
  if k = (0, 1) then |a| else if k = (1, 1) then ε / a else 0

end DuanCV.Gauss


