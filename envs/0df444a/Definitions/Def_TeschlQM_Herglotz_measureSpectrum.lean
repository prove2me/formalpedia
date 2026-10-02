-- Prove2me | Definitions.Def_TeschlQM_Herglotz_measureSpectrum
-- name    : TeschlQM_Herglotz_measureSpectrum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:33:15.253987+00:00
-- url     : https://prove2.me/theorems/9cb0b8ff-b94e-4df2-890d-9515a318b612
-- title:
--   Spectrum σ(μ) of a Borel measure: its set of growth points (3.59)
-- statement:
--   For a Borel measure $\mu$ on $\mathbb{R}$, a point $\lambda$ is a **growth point** of $\mu$ if every open interval centred at $\lambda$ has positive measure. The set of growth points is the **spectrum** of $\mu$:
--   $$\sigma(\mu) = \{\lambda \in \mathbb{R} \mid \mu((\lambda - \varepsilon, \lambda + \varepsilon)) > 0 \text{ for all } \varepsilon > 0\}.$$
--   It is the topological support of $\mu$, a closed set with $\mu(\mathbb{R} \setminus \sigma(\mu)) = 0$.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 99, Section 3.2, Eq. (3.59)

import Mathlib

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 99, (3.59): the **spectrum** of a Borel measure `μ` on `ℝ`, the set of its growth
points, `σ(μ) = {λ ∈ ℝ | μ((λ − ε, λ + ε)) > 0 for all ε > 0}`. -/
def measureSpectrum (μ : Measure ℝ) : Set ℝ :=
  {t : ℝ | ∀ ε : ℝ, 0 < ε → 0 < μ (Set.Ioo (t - ε) (t + ε))}

end TeschlQM.Herglotz


