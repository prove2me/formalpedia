-- Prove2me | Definitions.Def_TeschlQM_Herglotz_acPart
-- name    : TeschlQM_Herglotz_acPart
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:35:22.030227+00:00
-- url     : https://prove2.me/theorems/9b97c9fe-12a8-4d66-8c4a-14c84008ce82
-- title:
--   Absolutely continuous part μ_ac of a Borel measure (3.72)
-- statement:
--   Every $\sigma$-finite Borel measure $\mu$ on $\mathbb{R}$ decomposes uniquely as $d\mu = d\mu_{ac} + d\mu_s$, where $\mu_{ac}$ is absolutely continuous and $\mu_s$ is singular with respect to Lebesgue measure. The **absolutely continuous part** is
--   $$d\mu_{ac}(\lambda) = \frac{d\mu}{d\lambda}(\lambda)\, d\lambda,$$
--   the measure with density the Radon–Nikodym derivative of $\mu$ with respect to Lebesgue measure.
--
--   **Formalization Note.** `volume.withDensity (μ.rnDeriv volume)`, Mathlib's Lebesgue decomposition.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 102, Section 3.2, Eq. (3.72)

import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 102, (3.72): the **absolutely continuous part** `μ_ac` of a Borel measure `μ` on
`ℝ` in its Lebesgue decomposition `dμ = dμ_ac + dμ_s` with respect to Lebesgue measure,
`dμ_ac = (dμ/dλ) dλ`. -/
noncomputable def acPart (μ : Measure ℝ) : Measure ℝ :=
  volume.withDensity (μ.rnDeriv volume)

end TeschlQM.Herglotz


