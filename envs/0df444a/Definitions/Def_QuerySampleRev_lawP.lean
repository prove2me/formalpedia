-- Prove2me | Definitions.Def_QuerySampleRev_lawP
-- name    : QuerySampleRev_lawP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:42.256701+00:00
-- url     : https://prove2.me/theorems/8ab8aed8-6b3e-43fd-9c25-5745b0e96d9b
-- title:
--   Law $\mathbb P_{F,A}$ of a run under a value distribution
-- statement:
--   For a value distribution $\mu$, the law of a run is the product measure
--   $$
--   \mathbb P_\mu=\mathrm{Unif}[0,1]\otimes\mu^{\otimes\mathbb N}
--   $$
--   on outcomes $\omega=(u,v)$: the internal seed is uniform, and the values $v_0,v_1,\dots$ used by the successive sample or query rounds are i.i.d. with law $\mu$, independent of the seed. This is the paper's convention that every sample or query uses an independent draw from the value distribution. Probabilities $\mathbb P_{F^{(j)}}[\cdot]$ and expectations $\mathbb E_{F^{(j)}}[\cdot]$ over the transcript are taken under $\mathbb P_{F^{(j)}}$.
--
--   **Formalization Note** Expectations of counts are lower Lebesgue integrals with values in $[0,\infty]$.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §2.2, p.13 (PDF p.15); §2.3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QuerySampleRev_Learner

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **The law of a run under a value distribution, `P_{F,A}`.** Jin, Tang, Wang, Zhang, *Query-Sample
Tradeoffs for Revenue Maximization* (manuscript, sha256 c31ea3d3…), §2.2, p.13 (PDF 15): "Every sample or
query uses an independent draw from the value distribution"; "The probability is over the observations
generated from the fixed distribution `F` and the algorithm's internal randomness."

`lawP μ` is the product of the uniform law of the seed `u ∈ [0, 1]` and the i.i.d. law `μ^ℕ` of the
value stream `v`. The law `P⁽ⁱ⁾` of the transcript under `F⁽ⁱ⁾` (§2.3, p.14) is the image of
`lawP F⁽ⁱ⁾` under the transcript map, and expectations `E⁽ⁱ⁾` are lower Lebesgue integrals against
`lawP F⁽ⁱ⁾`. -/
noncomputable def lawP (μ : Measure ℝ) : Measure Outcome :=
  (volume : Measure unitInterval).prod (Measure.infinitePi fun _ : ℕ => μ)

end QuerySampleRev


