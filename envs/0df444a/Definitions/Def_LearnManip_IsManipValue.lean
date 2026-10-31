-- Prove2me | Definitions.Def_LearnManip_IsManipValue
-- name    : LearnManip_IsManipValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:12.80098+00:00
-- url     : https://prove2.me/theorems/9125c983-f3b8-4a6c-a694-b50052ec2edf
-- title:
--   $g$ solves the DP equation (15)
-- statement:
--   A function $g(s,c)$ solves (15) when, at every $s,c\ge0$,
--   $$g(s,c)=\sup_{q\ge0}\Bigl\{-cq+\alpha g\bigl(\tfrac{s}{1+sq},c\eta\bigr)+\frac{\sigma^2_{\mu^q}}{2\gamma(1-\alpha)^2}\Bigr\}.$$
--
--   **Formalization Note.** The paper's $\max$ is a least upper bound, which at $c=0$ is not attained (p.33).
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (15), p.13; (EC.15), p.ec9 (PDF 48)

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_manipObjective

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- `g` solves the DP equation (15), p.13, equivalently (EC.15), p.ec9 (PDF 48), of Keppo, Kim, Zhang
(SSRN 3465030, 2021-09-04), at every `(s, c)`.

**Formalization Note.** The paper's `max` is a least upper bound, `IsLUB`: at `c = 0` it is not attained
(the proof of Theorem 1, p.33: "`q* = ∞` when `c = 0`"). -/
def IsManipValue (P : Params) (g : ℝ≥0 → ℝ≥0 → ℝ) : Prop :=
  ∀ s c : ℝ≥0, IsLUB (Set.range (manipObjective P g s c)) (g s c)

end LearnManip


