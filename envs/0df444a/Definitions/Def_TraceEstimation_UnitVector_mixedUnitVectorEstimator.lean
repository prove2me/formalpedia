-- Prove2me | Definitions.Def_TraceEstimation_UnitVector_mixedUnitVectorEstimator
-- name    : TraceEstimation_UnitVector_mixedUnitVectorEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:36:56.108909+00:00
-- url     : https://prove2.me/theorems/abb6d709-4b01-45e5-ab94-4faf6fbf951c
-- title:
--   Definition 3.6 — the mixed unit vector trace estimator $T_M$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be symmetric positive semi-definite, $F$ an orthogonal seed matrix and $\mathcal F = FD$ the corresponding random mixing matrix, and let $M \ge 1$. The **mixed unit vector estimator** is
--
--   $$T_M = \frac{n}{M}\sum_{i=1}^{M} z_i^T \mathcal F A \mathcal F^T z_i ,$$
--
--   where $z_1, \ldots, z_M$ are $M$ independent uniform random samples from $\{e_1, \ldots, e_n\}$. In other words, $T_M$ is the unit vector estimator applied to the matrix $\mathcal F A \mathcal F^T$, which has the same trace as $A$; the mixing spreads the mass of $A$ over the diagonal so that no diagonal entry is much larger than the average.
--
--   **Formalization Note** The sample space is the product $(\mathbb{R}^n) \times \{1,\ldots,n\}^M$ carrying `mixedSampleMeasure n M = (signMeasure n).prod (indexSampleMeasure n M)`: the diagonal $d$ of $D$ and the indices $k_1,\ldots,k_M$ of the $z_i = e_{k_i}$ are independent of each other, which the paper assumes implicitly. `mixedUnitVectorEstimator F A M (d, k)` is `unitVectorEstimator (𝓕 * A * 𝓕ᵀ) M k` with `𝓕 = mixingMatrix F d`.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:4, Definition 3.6

import Mathlib
import Definitions.Def_TraceEstimation_UnitVector_unitVectorEstimator
import Definitions.Def_TraceEstimation_UnitVector_mixingMatrix

namespace TraceEstimation.UnitVector

open MeasureTheory Matrix

/-- The sample space of the mixed unit vector estimator with `M` samples in dimension `n`
(Avron–Toledo, Definition 3.6, p. 8:4): the Rademacher diagonal `d` of the mixing matrix
`𝓕 = F · diag(d)` and the `M` uniform indices `k_1, …, k_M`, drawn independently of each other
(product measure). -/
noncomputable def mixedSampleMeasure (n M : ℕ) : Measure ((Fin n → ℝ) × (Fin M → Fin n)) :=
  (signMeasure n).prod (indexSampleMeasure n M)

/-- The mixed unit vector estimator `T_M = (n/M) ∑_{i=1}^M z_iᵀ 𝓕 A 𝓕ᵀ z_i` of Definition 3.6
(Avron–Toledo, p. 8:4), with seed `F`, at the sample `ω = (d, k)`: `𝓕 = F · diag(d)` and
`z_i = e_{k_i}`. It is the unit vector estimator of the matrix `𝓕 A 𝓕ᵀ`. -/
noncomputable def mixedUnitVectorEstimator {n : ℕ} (F A : Matrix (Fin n) (Fin n) ℝ) (M : ℕ)
    (ω : (Fin n → ℝ) × (Fin M → Fin n)) : ℝ :=
  unitVectorEstimator (mixingMatrix F ω.1 * A * (mixingMatrix F ω.1)ᵀ) M ω.2

end TraceEstimation.UnitVector


