-- Prove2me | Definitions.Def_TraceEstimation_Rayleigh_rayleighEstimator
-- name    : TraceEstimation_Rayleigh_rayleighEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:19:31.640075+00:00
-- url     : https://prove2.me/theorems/76ad13f2-eaf9-4906-b86e-5f589ffc14bf
-- title:
--   Definition 3.2 — the normalized Rayleigh-quotient trace estimator $R_M$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be a symmetric positive semi-definite matrix and $M \ge 1$. A **normalized Rayleigh-quotient trace estimator** of $A$ is
--
--   $$R_M = \frac{1}{M}\sum_{i=1}^{M} z_i^T A z_i ,$$
--
--   where $z_1, \ldots, z_M$ are $M$ independent random vectors in $\mathbb{R}^n$ such that, for each $i$,
--
--   1. $z_i^T z_i = n$, and
--   2. $\mathrm{E}(z_i^T A z_i) = \mathrm{trace}(A)$.
--
--   The vectors need not be identically distributed, and the unbiasedness condition refers to this particular $A$. Examples: Hutchinson's vectors with i.i.d. Rademacher ($\pm 1$) entries, and $z = \sqrt{n}\,e_k$ with $k$ uniform on $\{1,\ldots,n\}$ (the unit vector estimator); both satisfy the two conditions for every $A$. Because $z_i^Tz_i = n$ bounds each sample $z_i^TAz_i$, this class admits a single general sample bound (Theorem 6.1).
--
--   **Formalization Note** The file contains two declarations. `rayleighEstimator A z ω` is the number $(M:\mathbb{R})^{-1}\sum_i z_i(\omega)^T A z_i(\omega)$ for random vectors `z : Fin M → Ω → Fin n → ℝ`. The structure `IsNormalizedRayleighSample P A z` collects the hypotheses of Definition 3.2 on a probability space $(\Omega, P)$: each $z_i$ is measurable, the family is mutually independent (`iIndepFun`), $z_i^Tz_i = n$ holds $P$-almost surely, and $\int z_i^TAz_i\,dP = \mathrm{trace}(A)$. The integrand is almost surely bounded in absolute value by $n^2\max_{j,k}|A_{jk}|$ (since $(\sum_j |z_j|)^2 \le n\, z^Tz$) and measurable, hence integrable, so the Bochner integral is the genuine expectation. For $M = 0$ the estimator is $0$; every theorem assumes $M \ge 1$.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:3, Definition 3.2

import Mathlib

namespace TraceEstimation.Rayleigh

open MeasureTheory ProbabilityTheory Matrix

/-- The estimate `R_M = (1/M) ∑_{i=1}^M z_iᵀ A z_i` of Definition 3.2 (Avron–Toledo, p. 8:3),
computed from `M` random vectors `z_1, …, z_M : Ω → ℝⁿ` at the outcome `ω`. -/
noncomputable def rayleighEstimator {Ω : Type*} {n M : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin M → Ω → Fin n → ℝ) (ω : Ω) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i : Fin M, z i ω ⬝ᵥ (A *ᵥ z i ω)

/-- The sampling hypotheses of Definition 3.2 (Avron–Toledo, p. 8:3): `z_1, …, z_M` are
`M` independent random vectors in `ℝⁿ` on the probability space `(Ω, P)` such that
`z_iᵀ z_i = n` (almost surely) and `E(z_iᵀ A z_i) = trace(A)`, for each `i`. With these
hypotheses `rayleighEstimator A z` is a normalized Rayleigh-quotient trace estimator of `A`.
The vectors need not be identically distributed. -/
structure IsNormalizedRayleighSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n M : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin M → Ω → Fin n → ℝ) : Prop where
  measurable : ∀ i, Measurable (z i)
  indep : iIndepFun z P
  normalized : ∀ i, ∀ᵐ ω ∂P, z i ω ⬝ᵥ z i ω = (n : ℝ)
  unbiased : ∀ i, ∫ ω, z i ω ⬝ᵥ (A *ᵥ z i ω) ∂P = A.trace

end TraceEstimation.Rayleigh


