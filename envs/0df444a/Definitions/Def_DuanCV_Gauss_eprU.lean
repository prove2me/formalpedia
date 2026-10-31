-- Prove2me | Definitions.Def_DuanCV_Gauss_eprU
-- name    : DuanCV_Gauss_eprU
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:37.55023+00:00
-- url     : https://prove2.me/theorems/4207d49e-639c-417f-be0d-61eecfed4d51
-- title:
--   The EPR-type operator $|a|\hat x_1+(\varepsilon/a)\hat x_2$
-- statement:
--   For real $a\neq0$ and a real $\varepsilon$, this is the coefficient vector on $(\hat x_1,\hat p_1,\hat x_2,\hat p_2)$ of
--
--   $$\hat u=|a|\,\hat x_1+\frac{\varepsilon}{a}\,\hat x_2 .$$
--
--   With $\varepsilon=1$ it is Eq. (2a). With $a=a_0>0$ and $\varepsilon=-c_1/|c_1|$ it is Eq. (15a).
--
--   **Formalization Note** The sign is a parameter, so that no quotient $c/|c|$ appears in Lean.
-- source:
--   Duan, Giedke, Cirac, Zoller, Inseparability criterion for continuous variable systems, arXiv:quant-ph/9908056v2, Eq. (2a), p. 1, and Eq. (15a), p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

namespace DuanCV.Gauss

/-- **The position-type EPR operator `|a| x̂₁ + (ε/a) x̂₂`, as a coefficient vector.**
Duan, Giedke, Cirac, Zoller, *Inseparability criterion for continuous variable systems*, arXiv:quant-ph/9908056v2, Eq. (2a), p. 1 and Eq. (15a), p. 4.

Coefficients on `(x̂₁, p̂₁, x̂₂, p̂₂)`, indexed by `QuadratureIndex 2` (`(j, 0)` = x̂ⱼ₊₁,
`(j, 1)` = p̂ⱼ₊₁). Eq. (2a) is `eprU a 1`. Eq. (15a) is `eprU a₀ (-ε₁)` with `a₀ > 0` and
`ε₁ = c₁/|c₁|`.

**Formalization Note.** The sign is a real parameter `ε`, so that no Lean division `c/|c|` occurs. -/
noncomputable def eprU (a ε : ℝ) : QuadratureIndex 2 → ℝ := fun k =>
  if k = (0, 0) then |a| else if k = (1, 0) then ε / a else 0

end DuanCV.Gauss


