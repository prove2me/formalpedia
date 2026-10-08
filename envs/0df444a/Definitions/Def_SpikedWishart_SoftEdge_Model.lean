-- Prove2me | Definitions.Def_SpikedWishart_SoftEdge_Model
-- name    : SpikedWishart_SoftEdge_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:38:41.857871+00:00
-- url     : https://prove2.me/theorems/f3d56de4-7d6c-4b0f-b347-3c9c93f0954c
-- title:
--   §1, pp. 1643–1645; (59) — complex Gaussian samples with covariance UΣU*, S = (1/M)Σ y_k y_k*, largest eigenvalue λ₁
-- statement:
--   This file fixes the probabilistic model of the paper: $M$ independent complex Gaussian samples of $N$ variables, their sample covariance matrix, and its largest eigenvalue.
--
--   A **standard complex Gaussian** is a random variable $g = a + ib$ with $a, b$ independent real normal variables of mean $0$ and variance $1/2$, so that $\mathbb E|g|^2 = 1$. Let $G = (g_{kj})_{1\le k\le M,\,1\le j\le N}$ be an array of i.i.d. standard complex Gaussians; its law on $\mathbb C^{M\times N}$ is the product measure $\mathbb P_{M,N}$.
--
--   The **population covariance** is $\Sigma = U\,\mathrm{diag}(\ell_1,\dots,\ell_N)\,U^*$ with $U$ an $N\times N$ unitary matrix and real eigenvalues $\ell_j$. The $k$-th sample is
--   $$
--   \vec y_k = U\,\mathrm{diag}(\sqrt{\ell_1},\dots,\sqrt{\ell_N})\,\vec g_k \in \mathbb C^N, \qquad \vec g_k = (g_{k1},\dots,g_{kN})^T,
--   $$
--   a mean-zero complex Gaussian vector with $\mathbb E\,\vec y_k\vec y_k^{\,*} = \Sigma$ when all $\ell_j > 0$. The **sample covariance matrix** is
--   $$
--   S = \frac1M\sum_{k=1}^M \vec y_k\,\vec y_k^{\,*},
--   $$
--   which is Hermitian (proved in the file), and $\lambda_1$ denotes its largest eigenvalue.
--
--   These are the objects of the paper's main theorems: every probability $\mathbb P(\lambda_1 \le \xi)$ in the mission is the $\mathbb P_{M,N}$-measure of $\{G : \lambda_1(S) \le \xi\}$.
--
--   **Formalization Note** The paper's printed model has three slips (p. 1645: density (1) "with the complex inner product", $S = \frac1N XX^*$, and centring by the sample mean); the formulas (59), (61) and Proposition 2.1 are those of mean-zero samples with $\mathbb E\,\vec y\vec y^{\,*} = \Sigma$, $S = \frac1M\sum_k \vec y_k\vec y_k^{\,*}$ and no centring, which is the model encoded here. The covariance is written in spectral form over every unitary $U$, not only diagonal $\Sigma$. $\lambda_1$ is the supremum of the Mathlib eigenvalues of the Hermitian matrix $S$ (the maximum for $N \ge 1$).
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1643–1645, §1, §1.1; p. 1655, (59)

import Mathlib

namespace SpikedWishart.SoftEdge

open MeasureTheory ProbabilityTheory

/-- The standard circularly-symmetric complex Gaussian law on `ℂ`: real and imaginary parts are
independent `N(0, 1/2)`, so that `E|g|² = 1`. -/
noncomputable def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map
    (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))

/-- The law of an `M × N` array `G k j` of i.i.d. standard complex Gaussians
(`k` indexes the `M` samples, `j` the `N` variables). -/
noncomputable def sampleLaw (M N : ℕ) : Measure (Fin M → Fin N → ℂ) :=
  Measure.pi fun _ => Measure.pi fun _ => stdComplexGaussian

/-- The `k`-th sample `y_k = U · diag(√ℓ) · g_k`, a mean-zero complex Gaussian vector with
covariance `Σ = U diag(ℓ) U*`. -/
noncomputable def sampleVec {M N : ℕ} (U : Matrix.unitaryGroup (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) (k : Fin M) : Fin N → ℂ :=
  Matrix.mulVec (U : Matrix (Fin N) (Fin N) ℂ) (fun j => (Real.sqrt (ℓ j) : ℂ) * G k j)

/-- The sample covariance matrix `S = (1/M) Σ_k y_k y_k*`. -/
noncomputable def sampleCov {N : ℕ} (M : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (M : ℂ)⁻¹ • ∑ k, Matrix.vecMulVec (sampleVec U ℓ G k) (star (sampleVec U ℓ G k))

theorem sampleCov_isHermitian {N : ℕ} (M : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (G : Fin M → Fin N → ℂ) : (sampleCov M U ℓ G).IsHermitian := by
  unfold sampleCov
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, star_sum, mul_comm]

/-- The largest eigenvalue `λ₁` of the sample covariance matrix. -/
noncomputable def largestEig {N : ℕ} (M : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (G : Fin M → Fin N → ℂ) : ℝ :=
  ⨆ i, (sampleCov_isHermitian M U ℓ G).eigenvalues i

end SpikedWishart.SoftEdge


