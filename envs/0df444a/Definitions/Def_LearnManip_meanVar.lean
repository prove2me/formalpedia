-- Prove2me | Definitions.Def_LearnManip_meanVar
-- name    : LearnManip_meanVar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:40.718186+00:00
-- url     : https://prove2.me/theorems/c7d9a3bb-11b2-4c15-ab2a-f9d12f2681a5
-- title:
--   Variance of the posterior mean $\sigma^2_{\mu^q}=s^2q/(1+sq)$
-- statement:
--   The variance of the undistorted posterior mean $\mu^q$, unconditional on the signal, for prior variance $s\ge0$ and quantity $q\ge0$:
--   $$\sigma^2_{\mu^q}=\frac{s^2q}{1+sq}.$$
--   It equals $s-s^q$, the variance removed by the signal, and it is the room the firm has for distortion.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (3), p.8

import Mathlib

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The variance `σ²_{μ^q} = s² q / (1 + s q)` of the undistorted posterior mean, (3), p.8, of Keppo,
Kim, Zhang (SSRN 3465030, 2021-09-04). -/
noncomputable def meanVar (s q : ℝ≥0) : ℝ≥0 := s ^ 2 * q / (1 + s * q)

end LearnManip


