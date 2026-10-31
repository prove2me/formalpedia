-- Prove2me | Definitions.Def_LearnManip_varPath
-- name    : LearnManip_varPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:39.991126+00:00
-- url     : https://prove2.me/theorems/7abed46e-2c53-45f4-863a-67d1f3a7934a
-- title:
--   The variance path $s_n$ along a history
-- statement:
--   For a quantity rule $q$ and prior variance $s_0$, the variance after a history is defined recursively by
--   $$s_{n+1}=\frac{s_n}{1+s_nq_{n+1}},$$
--   where $q_{n+1}$ is the rule evaluated on the history up to $n$. By (5) the update does not involve the distortion.
--
--   **Formalization Note.** Periods are indexed from $0$ in Lean: `q n` is the quantity of the paper's period $t=n+1$.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (2), p.7, and (5), p.8

import Mathlib
import Definitions.Def_LearnManip_postVar
import Definitions.Def_LearnManip_History

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The posterior variance along a history under a quantity rule `q`: `s_0 = s₀` and
`s_{n+1} = s_n / (1 + s_n q_{n+1})`, by (2) and (5), pp.7–8, of Keppo, Kim, Zhang (SSRN 3465030,
2021-09-04). The update ignores the distortion, as in (5). Periods are indexed from `0` in Lean, so
`q n` is the quantity of the paper's period `t = n + 1`. -/
noncomputable def varPath (q : (n : ℕ) → History n → ℝ≥0) (s₀ : ℝ≥0) :
    (n : ℕ) → History n → ℝ≥0
  | 0, _ => s₀
  | n + 1, h =>
      postVar (varPath q s₀ n (History.prefix h)) (q n (History.prefix h))

end LearnManip


