-- Prove2me | Definitions.Def_TraceEstimation_Shared_gaussianEstimator
-- name    : TraceEstimation_Shared_gaussianEstimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:26:23.978229+00:00
-- url     : https://prove2.me/theorems/d5fd3817-2a5c-45c9-b770-be6880efb562
-- title:
--   Definition 3.1 — the Gaussian trace estimator $G_M$
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ and let $M \ge 1$ be the number of samples. Draw $M$ random vectors $z_1, \ldots, z_M \in \mathbb{R}^n$ whose $Mn$ entries are independent standard normal random variables. The **Gaussian trace estimator** is
--
--   $$G_M = \frac{1}{M}\sum_{i=1}^{M} z_i^T A z_i .$$
--
--   This file fixes the probability space on which $G_M$ lives: the sample space is the set of $M$-tuples $(z_1,\ldots,z_M)$ of vectors in $\mathbb{R}^n$, equipped with the product of $Mn$ copies of the standard normal law $N(0,1)$. The estimator is then an explicit function of the sample, so its law is constructed rather than assumed.
--
--   The Gaussian estimator is the first of the randomized trace estimators analysed by Avron and Toledo; it needs only $M$ matrix–vector products with $A$, which is why it applies to matrices available only implicitly.
--
--   **Formalization Note** The sample space is `Fin M → Fin n → ℝ` with the measure `Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 1))` (named `gaussianSampleMeasure n M`), and $G_M(\omega) = (M:\mathbb{R})^{-1}\sum_i \omega_i \cdot (A\,\omega_i)$. Definition 3.1 says "symmetric positive-definite", but the definition of $G_M$ makes sense for every square matrix, so no hypothesis on $A$ is built into it; each theorem states the hypothesis it needs. For $M = 0$ the formula returns $0$; every theorem that uses it assumes $M \ge 1$.
--
--   **Shared definition.** This is the group's single copy of this definition, reviewed once for every chunk that uses it: `01-gaussian` (Theorem 5.2: Lemma 5.1 p. 8:7, Section 5 Eq. (1) pp. 8:7–8:8, the tail bounds in the proof of Theorem 5.2 pp. 8:8–8:9, Theorem 5.2 p. 8:7); `02-projection-rank` (Lemma 5.3 and its proof, p. 8:9).
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:3, Definition 3.1

import Mathlib

namespace TraceEstimation.Shared

open MeasureTheory ProbabilityTheory Matrix

/-- The sample space of the Gaussian trace estimator with `M` samples in dimension `n`:
`M` random vectors `z_1, …, z_M ∈ ℝⁿ` whose `M·n` entries are i.i.d. standard normal
(Avron–Toledo, Definition 3.1, p. 8:3). It is the product of `M · n` copies of `N(0,1)`. -/
noncomputable def gaussianSampleMeasure (n M : ℕ) : Measure (Fin M → Fin n → ℝ) :=
  Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- The Gaussian trace estimator `G_M = (1/M) ∑_{i=1}^M z_iᵀ A z_i` of Definition 3.1
(Avron–Toledo, p. 8:3), as a function of the sample `ω = (z_1, …, z_M)`. -/
noncomputable def gaussianEstimator {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (M : ℕ)
    (ω : Fin M → Fin n → ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i : Fin M, ω i ⬝ᵥ (A *ᵥ ω i)

end TraceEstimation.Shared


