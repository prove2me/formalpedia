-- Prove2me | Definitions.Def_LearnManip_postVar
-- name    : LearnManip_postVar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:42.535887+00:00
-- url     : https://prove2.me/theorems/58efab99-3ab5-400e-bcc6-240c6b9c5272
-- title:
--   Posterior variance $s^q=s/(1+sq)$
-- statement:
--   The variance of the public's posterior after a quantity $q\ge0$ of Gaussian information, under prior variance $s\ge0$:
--   $$s^q=\frac{s}{1+sq}.$$
--   By (5) the public applies this update whatever the firm's distortion, so the variance is a deterministic function of the quantities chosen.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (2), p.7

import Mathlib

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The posterior variance `s^q = s / (1 + s q)` of (2), p.7, of Keppo, Kim, Zhang (SSRN 3465030,
2021-09-04), after a quantity `q` of Gaussian information is disseminated under prior variance `s`.

**Formalization Note.** Variances and quantities are `ℝ≥0`; `1 + s q ≥ 1`, so the division is
genuine. -/
noncomputable def postVar (s q : ℝ≥0) : ℝ≥0 := s / (1 + s * q)

end LearnManip


