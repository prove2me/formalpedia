-- Prove2me | Definitions.Def_SpikedWishart_LastPassage_Model
-- name    : SpikedWishart_LastPassage_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:09.85311+00:00
-- url     : https://prove2.me/theorems/34e8fde4-aaa8-4b31-a5da-12bd52cf69ee
-- title:
--   §1, pp. 1643–1645; (59) — complex Gaussian samples with covariance U diag(ℓ) U*, S = (1/M)Σ y_k y_k*, largest eigenvalue λ₁
-- statement:
--   This file fixes the sample model of the paper.
--
--   A **standard complex Gaussian** $g$ is a complex random variable whose real and imaginary parts are independent centred normal variables of variance $1/2$, so that $\mathbb E|g|^2 = 1$. Let $G = (g_{kj})$, $k = 1, \ldots, M$, $j = 1, \ldots, N$, be an array of independent standard complex Gaussians; its law is the product measure on $\mathbb C^{M\times N}$.
--
--   Given a unitary $N\times N$ matrix $U$ and positive numbers $\ell_1, \ldots, \ell_N$, the $k$-th **sample** is the vector
--   $$\vec y_k = U\,\mathrm{diag}(\sqrt{\ell_1}, \ldots, \sqrt{\ell_N})\, g_k \in \mathbb C^N, \qquad g_k = (g_{k1}, \ldots, g_{kN})^T,$$
--   a mean-zero complex Gaussian vector with covariance $\Sigma = U\,\mathrm{diag}(\ell_1,\ldots,\ell_N)\,U^*$. Every positive definite Hermitian $\Sigma$ arises this way. The **sample covariance matrix** is
--   $$S = \frac1M \sum_{k=1}^M \vec y_k\, \vec y_k^{\,*},$$
--   a Hermitian $N\times N$ matrix, and $\lambda_1$ denotes its **largest eigenvalue**.
--
--   These are the objects of the paper's Introduction; the eigenvalue $\lambda_1$ is the random variable whose law Proposition 6.1 identifies with that of a last passage time.
--
--   **Formalization Note** The samples are mean zero and are not centred by the sample mean, and the normalisation is $1/M$; this is the model of (59), (61) and (307), and it is the reading under which Proposition 6.1 is an exact identity (the page's centring by the sample mean and its $S = (1/N)XX^*$ on p. 1645 are printed slips). The covariance is $U\,\mathrm{diag}(\ell)\,U^*$ for an arbitrary unitary $U$, not only a diagonal $\Sigma$. The largest eigenvalue is the supremum of the eigenvalues that Mathlib attaches to the Hermitian matrix $S$. The same declarations appear in the other missions of this series under their own namespaces.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1643, §1; p. 1645, §1.1; p. 1655, (59)

import Mathlib
import Definitions.Def_SpikedWishart_SoftEdge_Model

namespace SpikedWishart.LastPassage

open MeasureTheory ProbabilityTheory

/-- The standard circularly-symmetric complex Gaussian law on `ℂ`: real and imaginary parts are
independent `N(0, 1/2)`, so that `E|g|² = 1`. -/
noncomputable def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))).map
    (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))

instance stdComplexGaussian.instIsProbabilityMeasure :
    IsProbabilityMeasure stdComplexGaussian :=
  Measure.isProbabilityMeasure_map (Complex.measurableEquivRealProd.symm.measurable.aemeasurable)

/-- The law of an `M × N` array `G k j` of i.i.d. standard complex Gaussians
(`k` indexes the `M` samples, `j` the `N` variables). -/
noncomputable def sampleLaw (M N : ℕ) : Measure (Fin M → Fin N → ℂ) :=
  Measure.pi fun _ => Measure.pi fun _ => stdComplexGaussian

instance sampleLaw.instIsProbabilityMeasure (M N : ℕ) : IsProbabilityMeasure (sampleLaw M N) := by
  unfold sampleLaw; infer_instance

theorem sampleCov_isHermitian {N : ℕ} (M : ℕ) (U : Matrix.unitaryGroup (Fin N) ℂ)
    (ℓ : Fin N → ℝ) (G : Fin M → Fin N → ℂ) : (SpikedWishart.SoftEdge.sampleCov M U ℓ G).IsHermitian := by
  unfold SpikedWishart.SoftEdge.sampleCov
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, star_sum, mul_comm]

end SpikedWishart.LastPassage


