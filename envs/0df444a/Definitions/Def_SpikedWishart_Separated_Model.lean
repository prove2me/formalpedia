-- Prove2me | Definitions.Def_SpikedWishart_Separated_Model
-- name    : SpikedWishart_Separated_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:24.722634+00:00
-- url     : https://prove2.me/theorems/d33928dc-7e6e-4339-8826-02ebc603feb4
-- title:
--   §1, pp. 1643–1645; (59) — samples y_k = U diag(√ℓ) g_k, S = (1/M)Σ y_k y_k*, largest eigenvalue λ₁ (matrix U as a parameter)
-- statement:
--   This file builds the sample covariance matrix and its largest eigenvalue on top of the Gaussian sample law of `SpikedWishart.SoftEdge.Model`.
--
--   Let $G = (G_{kj})_{k \le M,\ j \le N}$ be an $M \times N$ array of independent standard complex Gaussians ($G_{kj} = a + ib$ with $a, b$ independent real normal variables of mean $0$ and variance $1/2$, so $\mathbb E|G_{kj}|^2 = 1$); its law is the **sample law** $\mathbb P_{M,N}$ on $\mathbb C^{M \times N}$, defined in `SpikedWishart.SoftEdge.Model`. This file records that $\mathbb P_{M,N}$ and the one-coordinate law are probability measures.
--
--   Given an $N \times N$ complex matrix $U$ and real numbers $\ell_1, \dots, \ell_N$, the $k$-th sample is
--   $$
--   \vec y_k = U \,\mathrm{diag}\big(\sqrt{\ell_1}, \dots, \sqrt{\ell_N}\big)\, \vec g_k, \qquad \vec g_k = (G_{k1}, \dots, G_{kN})^{\mathsf T}.
--   $$
--   When $U$ is unitary and every $\ell_j > 0$, $\vec y_k$ is a mean-zero complex Gaussian vector with covariance $\Sigma = U\,\mathrm{diag}(\ell_1,\dots,\ell_N)\,U^*$, and every positive-definite Hermitian $\Sigma$ arises this way. The **sample covariance matrix** is
--   $$
--   S = \frac1M \sum_{k=1}^M \vec y_k\, \vec y_k^{\,*},
--   $$
--   a Hermitian $N\times N$ matrix (proved in the file), and $\lambda_1$ denotes its **largest eigenvalue**.
--
--   These are the objects of the paper's Theorem 1.1(b), Corollary 1.1(b) and Proposition 1.1: each probability $\mathbb P(\lambda_1 \le \xi)$ there is the $\mathbb P_{M,N}$-measure of $\{G : \lambda_1(S) \le \xi\}$.
--
--   **Formalization Note** $U$ is an arbitrary complex matrix in the definitions; the theorems that use them assume $U$ unitary (or take $U = I$ where the paper fixes $\Sigma = \ell_1 I$) and $\ell_j > 0$ (for $\ell_j < 0$, `Real.sqrt` would return $0$). The samples are mean zero and not centred by the sample mean, and $S$ carries the factor $1/M$; this is the model of the paper's formulas (59), (61) and Proposition 2.1 (the text on pp. 1643–1645 also mentions $1/N$, centring by $\bar Y$ and the real density (1), which are inconsistent with those formulas). $\lambda_1$ is the supremum of the eigenvalues returned by Mathlib's spectral theorem for Hermitian matrices; it is the maximum for $N \ge 1$ (for $N = 0$ it is the junk value $0$), and every statement using it has $N \ge 1$.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1643–1645, §1, §1.1; p. 1655, (59)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Model

open MeasureTheory ProbabilityTheory Matrix

namespace SpikedWishart.Separated

instance : IsProbabilityMeasure SpikedWishart.SoftEdge.stdComplexGaussian := by
  unfold SpikedWishart.SoftEdge.stdComplexGaussian
  exact Measure.isProbabilityMeasure_map
    Complex.measurableEquivRealProd.symm.measurable.aemeasurable

instance (M N : ℕ) : IsProbabilityMeasure (SpikedWishart.SoftEdge.sampleLaw M N) := by
  unfold SpikedWishart.SoftEdge.sampleLaw
  infer_instance

/-- The `k`-th sample `y_k = U · diag(√ℓ) · g_k`, a mean-zero complex Gaussian vector with
covariance `Σ = U diag(ℓ) U*` when `U` is unitary. -/
noncomputable def sampleVec {M N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) (k : Fin M) : Fin N → ℂ :=
  U *ᵥ (fun j => (Real.sqrt (ℓ j) : ℂ) * G k j)

/-- The sample covariance matrix `S = (1/M) Σ_k y_k y_k*` (mean zero, no centring). -/
noncomputable def sampleCov (M : ℕ) {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (M : ℂ)⁻¹ • ∑ k, Matrix.vecMulVec (sampleVec U ℓ G k) (star (sampleVec U ℓ G k))

theorem sampleCov_isHermitian (M : ℕ) {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) : (sampleCov M U ℓ G).IsHermitian := by
  unfold sampleCov
  refine IsHermitian.smul ?_ ?_
  · unfold IsHermitian
    rw [conjTranspose_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [conjTranspose_vecMulVec, star_star]
  · simp [IsSelfAdjoint]

/-- The largest eigenvalue `λ₁` of the sample covariance matrix. -/
noncomputable def largestEig (M : ℕ) {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) : ℝ :=
  ⨆ i, (sampleCov_isHermitian M U ℓ G).eigenvalues i

end SpikedWishart.Separated


