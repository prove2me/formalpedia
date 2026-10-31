-- Prove2me | Definitions.Def_LearnManip_boost
-- name    : LearnManip_boost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:47.713063+00:00
-- url     : https://prove2.me/theorems/d2fab3ca-1216-4d3a-a7cb-ca227a43255f
-- title:
--   Optimal mean boost $\Delta^*(s,c)$
-- statement:
--   The optimal mean boost
--   $$\Delta^*(s,c)=\frac{(s-s_{TH}(c))^+}{(1-\alpha)\gamma}.$$
--
--   **Formalization Note.** The subtraction is in the nonnegative reals, so it is exactly the positive part.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (20), p.17, and the end of the proof of Theorem 2, p.35

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_sTH

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The optimal mean boost (20), `∆*(s, c) = (s − s_TH(c))⁺ / ((1−α)γ)`, p.17, of Keppo, Kim, Zhang
(SSRN 3465030, 2021-09-04).

**Formalization Note.** The subtraction is in `ℝ≥0`, so `s - sTH P c` is exactly the positive part
`(s − s_TH(c))⁺`. -/
noncomputable def boost (P : Params) (s c : ℝ≥0) : ℝ :=
  ((s - sTH P c : ℝ≥0) : ℝ) / ((1 - (P.α : ℝ)) * (P.γ : ℝ))

end LearnManip


