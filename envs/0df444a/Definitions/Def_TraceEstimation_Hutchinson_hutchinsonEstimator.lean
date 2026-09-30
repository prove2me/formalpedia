-- Prove2me | Definitions.Def_TraceEstimation_Hutchinson_hutchinsonEstimator
-- name    : TraceEstimation_Hutchinson_hutchinsonEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:26:29.664761+00:00
-- url     : https://prove2.me/theorems/99dfd173-3b2d-4d0a-85a6-2f9f4c4b5e70
-- title:
--   Definition 3.3 — Hutchinson's trace estimator $H_M$
-- statement:
--   A **Rademacher** random variable takes the values $+1$ and $-1$, each with probability $1/2$. Let $A \in \mathbb{R}^{n\times n}$ and let $M \ge 1$ be the number of samples. Draw $M$ independent random vectors $z_1, \ldots, z_M \in \mathbb{R}^n$ whose $Mn$ entries are independent Rademacher random variables. **Hutchinson's trace estimator** is
--
--   $$H_M = \frac{1}{M}\sum_{i=1}^{M} z_i^T A z_i .$$
--
--   This file fixes the probability space on which $H_M$ lives. The Rademacher law on $\mathbb{R}$ is $\tfrac12(\delta_{1} + \delta_{-1})$; the law of one sample vector $z$ is the product of $n$ copies of it; and the sample space is the set of $M$-tuples $(z_1,\ldots,z_M)$ with the product of $M$ copies of the vector law. The estimator is then an explicit function of the sample, so its law is constructed rather than assumed.
--
--   Hutchinson's estimator is the standard Monte-Carlo method for the trace of a matrix available only through matrix–vector products; it uses one random bit per entry and only additions and subtractions.
--
--   **Formalization Note** `rademacher` is `(2⁻¹ : ℝ≥0∞) • (dirac 1 + dirac (-1))` on `ℝ`, with an instance showing it is a probability measure. `rademacherVectorMeasure n` is `Measure.pi` of $n$ copies, and `hutchinsonSampleMeasure n M` is `Measure.pi` of $M$ copies of that, on `Fin M → Fin n → ℝ`. $H_M(\omega) = (M:\mathbb{R})^{-1}\sum_i \omega_i \cdot (A\,\omega_i)$. Definition 3.3 says "symmetric positive-definite", but the formula makes sense for every square matrix, so no hypothesis on $A$ is built in; each theorem states the hypothesis it needs. For $M = 0$ the formula returns $0$.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:3, Definition 3.3 (Rademacher law as in Lemma 2.1, p. 8:2)

import Mathlib

namespace TraceEstimation.Hutchinson

open MeasureTheory ProbabilityTheory Matrix

/-- The Rademacher law on `ℝ`: the values `1` and `-1`, each with probability `1/2`
(Avron–Toledo, Lemma 2.1 and Lemma 7.2: `Pr(z_i = ±1) = 1/2`). -/
noncomputable def rademacher : Measure ℝ :=
  (2⁻¹ : ENNReal) • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))

instance rademacher_isProbabilityMeasure : IsProbabilityMeasure rademacher := by
  constructor
  simp only [rademacher, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The law of one Rademacher vector `z ∈ ℝⁿ`: its `n` entries are i.i.d. Rademacher. -/
noncomputable def rademacherVectorMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => rademacher

/-- The sample space of Hutchinson's trace estimator with `M` samples in dimension `n`:
`M` independent random vectors `z_1, …, z_M ∈ ℝⁿ` whose `M·n` entries are i.i.d. Rademacher
(Avron–Toledo, Definition 3.3, p. 8:3). -/
noncomputable def hutchinsonSampleMeasure (n M : ℕ) : Measure (Fin M → Fin n → ℝ) :=
  Measure.pi fun _ : Fin M => rademacherVectorMeasure n

/-- Hutchinson's trace estimator `H_M = (1/M) ∑_{i=1}^M z_iᵀ A z_i` of Definition 3.3
(Avron–Toledo, p. 8:3), as a function of the sample `ω = (z_1, …, z_M)`. -/
noncomputable def hutchinsonEstimator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (M : ℕ)
    (ω : Fin M → Fin n → ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i : Fin M, ω i ⬝ᵥ (A *ᵥ ω i)

end TraceEstimation.Hutchinson


