-- Prove2me | Definitions.Def_LearnManip_qStar
-- name    : LearnManip_qStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:36.816835+00:00
-- url     : https://prove2.me/theorems/b8d600f0-ad36-4c99-96e3-515d386ceef1
-- title:
--   Optimal dissemination quantity $q^*(s,c)$
-- statement:
--   The optimal dissemination quantity
--   $$q^*(s,c)=\Bigl(\frac{1}{s_{TH}(c)}-\frac1s\Bigr)^+.$$
--   It is $0$ when $s\le s_{TH}(c)$, and otherwise it brings the variance to exactly $s_{TH}(c)$.
--
--   **Formalization Note.** At $s=0$ the formula reads $1/s=\infty$ and $q^*=0$, which the case split gives. At $c=0$ the paper has $q^*=\infty$ (p.33), which is not a quantity; the definition is used only for $c>0$.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (17), p.15

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_sTH

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

open Classical in
/-- The optimal dissemination quantity (17), `q*(s, c) = (1/s_TH(c) − 1/s)⁺`, p.15, of Keppo, Kim,
Zhang (SSRN 3465030, 2021-09-04), with `s_TH` at `η̄ = min(η, 1)`.

**Formalization Note.** The `if` is the positive part, including `s = 0`, where (17) reads
`1/s = ∞` and `q* = 0`; in Lean `1/0 = 0` would give the wrong value. For `s > s_TH(c)` the `ℝ≥0`
subtraction is genuine when `c > 0`. At `c = 0` the paper has `q* = ∞` (p.33), which is not in `ℝ₊`;
`qStar` is used only for `c > 0`. -/
noncomputable def qStar (P : Params) (s c : ℝ≥0) : ℝ≥0 :=
  if s ≤ sTH P c then 0 else 1 / sTH P c - 1 / s

end LearnManip


