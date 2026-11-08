-- Prove2me | Definitions.Def_SpencerEight_gaussF
-- name    : SpencerEight_gaussF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:56.356557+00:00
-- url     : https://prove2.me/theorems/9b8ade16-2dc0-4da9-a228-6dcbb73de3ba
-- title:
--   Gaussian interval mass $F(x)=\gamma_1([-x,x])$
-- statement:
--   $F(x):=\gamma_1([-x,x])$, the standard Gaussian mass of the centered interval, used in Eq. (59).
--
--   **Formalization Note** The real number obtained by `toReal` from a probability, which is finite.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), proof of Lemma 8.2, p.69 (PDF p.69)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace SpencerEight

/-- `F(x) := γ₁([−x, x])` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), proof of Lemma 8.2, p.69 (PDF p.69)), as a real number.

**Formalization Note** `toReal` of a probability, which is finite. -/
noncomputable def gaussF (x : ℝ) : ℝ := (gaussianReal 0 1 (Set.Icc (-x) x)).toReal

end SpencerEight


