-- Prove2me | Definitions.Def_TraceEstimation_UnitVector_unitVectorEstimator
-- name    : TraceEstimation_UnitVector_unitVectorEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:33:54.896358+00:00
-- url     : https://prove2.me/theorems/b3b7d008-e86f-466d-8035-6b2b1650d323
-- title:
--   Definition 3.4 — the unit vector trace estimator $U_M$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ with $n \ge 1$, let $e_1, \ldots, e_n$ be the standard basis vectors of $\mathbb{R}^n$, and let $M \ge 1$. The **unit vector estimator** of $\mathrm{trace}(A)$ is
--
--   $$U_M = \frac{n}{M}\sum_{i=1}^{M} z_i^T A z_i ,$$
--
--   where $z_1, \ldots, z_M$ are $M$ independent uniform random samples from $\{e_1, \ldots, e_n\}$ (drawn with replacement). Writing $z_i = e_{k_i}$ with $k_i$ uniform on $\{1,\ldots,n\}$, each term $z_i^TAz_i = A_{k_ik_i}$ is a diagonal entry of $A$ chosen at random, so a sample needs only $\lceil \log_2 n\rceil$ random bits.
--
--   The file also defines the sample space: the uniform law on the index set $\{1,\ldots,n\}$ and its $M$-fold product, the law of $(k_1,\ldots,k_M)$.
--
--   **Formalization Note** Indices live in `Fin n`. `uniformIndex n` is Mathlib's `uniformOn Set.univ` on `Fin n` (a probability measure exactly when $n \ge 1$); `indexSampleMeasure n M` is the product measure `Measure.pi` of $M$ copies, which makes the samples independent. `unitVectorEstimator A M k` is $(n/M)\sum_i e_{k_i}^T A e_{k_i}$ with $e_k$ written `Pi.single k 1`. The paper's Definition 3.4 says "positive-definite"; the definition itself makes sense for any square matrix, and each theorem states the hypothesis on $A$ it needs.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:4, Definition 3.4

import Mathlib

namespace TraceEstimation.UnitVector

open MeasureTheory ProbabilityTheory Matrix

/-- The uniform probability law on the index set `{1, …, n}` (here `Fin n`): each index `k`,
i.e. each standard basis vector `e_k`, has probability `1/n`. It is a probability measure
exactly when `n > 0`. -/
noncomputable def uniformIndex (n : ℕ) : Measure (Fin n) :=
  uniformOn (Set.univ : Set (Fin n))

/-- The sample space of the unit vector estimator with `M` samples in dimension `n`:
`M` independent indices `k_1, …, k_M`, each uniform on `Fin n` (so the samples
`z_i = e_{k_i}` are `M` independent uniform random samples from `{e_1, …, e_n}`, drawn with
replacement; Avron–Toledo, Definition 3.4, p. 8:4). -/
noncomputable def indexSampleMeasure (n M : ℕ) : Measure (Fin M → Fin n) :=
  Measure.pi fun _ : Fin M => uniformIndex n

/-- The unit vector estimator `U_M = (n/M) ∑_{i=1}^M z_iᵀ A z_i` of Definition 3.4
(Avron–Toledo, p. 8:4), as a function of the sample `k = (k_1, …, k_M)`, where
`z_i = e_{k_i}` is the `k_i`-th standard basis vector of `ℝⁿ`. -/
noncomputable def unitVectorEstimator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (M : ℕ)
    (k : Fin M → Fin n) : ℝ :=
  (n : ℝ) / (M : ℝ) *
    ∑ i : Fin M, (Pi.single (k i) (1 : ℝ) : Fin n → ℝ) ⬝ᵥ (A *ᵥ (Pi.single (k i) (1 : ℝ)))

end TraceEstimation.UnitVector


