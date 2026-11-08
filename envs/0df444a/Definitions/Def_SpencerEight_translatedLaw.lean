-- Prove2me | Definitions.Def_SpencerEight_translatedLaw
-- name    : SpencerEight_translatedLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:27.720134+00:00
-- url     : https://prove2.me/theorems/48e629bd-2992-4ce0-bea0-7c82d3711c6a
-- title:
--   Law $P$ of $Z+s\sigma$
-- statement:
--   Let $Z$ have the density $f_Z$ and let $\sigma$ be a uniform sign independent of $Z$. The measure $P$ on $\mathbb R$ is the law of $Z+s\sigma$.
--
--   Lemma 8.2 compares $P$ with the standard Gaussian.
--
--   **Formalization Note** The image under $(z,\sigma)\mapsto z+s\sigma$ of the product of the measure with density $f_Z$ and $\tfrac12\delta_1+\tfrac12\delta_{-1}$.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 8.1 and Lemma 8.2, p.69 (PDF p.69)

import Mathlib
import Definitions.Def_SpencerEight_densityZ
open MeasureTheory
open scoped ENNReal

namespace SpencerEight

/-- The law `P` of `Z + sσ` (Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Lemma 8.2, p.69 (PDF p.69)), where `Z` has density `f_Z` and `σ` is a uniform sign independent of `Z`.

**Formalization Note** The law of the sum under the product of the law of `Z` and the uniform law on `{1, −1}`: the page's construction, not a density written down in advance. The map `(z, σ) ↦ z + sσ` is continuous, so the image measure is genuine. -/
noncomputable def translatedLaw (s a : ℝ) : Measure ℝ :=
  ((volume.withDensity fun z => ENNReal.ofReal (densityZ s a z)).prod
      ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℝ) + (1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℝ))).map
    fun p => p.1 + s * p.2

end SpencerEight


