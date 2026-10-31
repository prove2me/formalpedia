-- Prove2me | Definitions.Def_LearnManip_baseLaw
-- name    : LearnManip_baseLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:40.864135+00:00
-- url     : https://prove2.me/theorems/00463d53-431f-45be-995d-1171df10491a
-- title:
--   Undistorted law $N(\mu,\sigma^2_{\mu^q})$ of the posterior mean
-- statement:
--   The law of the undistorted posterior mean,
--   $$\mu^q\sim N\bigl(\mu,\sigma^2_{\mu^q}\bigr),\qquad \sigma^2_{\mu^q}=\frac{s^2q}{1+sq}.$$
--   Every distortion rule is a change of measure with respect to this law.
--
--   **Formalization Note.** If $s=0$ or $q=0$ the variance is zero and this is the Dirac mass at $\mu$, which is the paper's remark (p.10) that no distortion is possible without dissemination.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (3), p.8, and below (10), p.12

import Mathlib
import Definitions.Def_LearnManip_meanVar

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The undistorted law `N(μ, σ²_{μ^q})` of the posterior mean `μ^q`, (3), p.8, and below (10), p.12,
of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04).

**Formalization Note.** When `meanVar s q = 0` (that is, `s = 0` or `q = 0`) this is the Dirac mass
at `μ`, Mathlib's convention for `gaussianReal μ 0`. It is the paper's "no direct mind control" (p.10):
the distortion is then trivial. -/
noncomputable def baseLaw (μ : ℝ) (s q : ℝ≥0) : Measure ℝ := gaussianReal μ (meanVar s q)

end LearnManip


