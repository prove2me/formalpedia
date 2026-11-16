-- Prove2me | Definitions.Def_GeomDRSub_Supplement_C
-- name    : GeomDRSub_Supplement_C
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:50:44.745658+00:00
-- url     : https://prove2.me/theorems/fef94e89-ada5-4059-aaa3-ede44ab8a52a
-- title:
--   The explicit geometric bound $C(\zeta)$, extended by $1/2$
-- statement:
--   $$C(\zeta)=\begin{cases}63/128,&0\le\zeta\le1/4,\\[2pt] \dfrac12-\dfrac{(1-2\zeta)^2}{2(1+2\sqrt\zeta)^4},&1/4\le\zeta<1/2,\\[4pt] 1/2,&1/2\le\zeta\le1.\end{cases}$$
--
--   The first two pieces are Eq. (180) of Lemma 6.7, and they agree at $\zeta=1/4$. The extension by $1/2$ for $\zeta\ge1/2$ is stated before (186).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Lemma 6.7, p.45, Eq. (180), and Section 6.5, p.46

import Mathlib

namespace GeomDRSub.Supplement

/-- **The explicit geometric bound `C(ζ)`**, Eq. (180), extended by `1/2`. Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545,
Lemma 6.7, p.45: `C(ζ) = 63/128` for `0 ≤ ζ ≤ 1/4` and
`C(ζ) = 1/2 − (1 − 2ζ)²/(2(1 + 2√ζ)⁴)` for `1/4 ≤ ζ < 1/2`; Section 6.5, p.46: "Extend `C(ζ) = 1/2`
for `ζ ≥ 1/2`". The two formulas agree at `ζ = 1/4` (both equal `63/128`). Only `ζ ∈ [0,1]` is
used. -/
noncomputable def C (ζ : ℝ) : ℝ :=
  if ζ ≤ 1 / 4 then 63 / 128
  else if ζ < 1 / 2 then 1 / 2 - (1 - 2 * ζ) ^ 2 / (2 * (1 + 2 * Real.sqrt ζ) ^ 4)
  else 1 / 2

end GeomDRSub.Supplement


