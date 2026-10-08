-- Prove2me | Definitions.Def_SpikedWishart_FixedDim_Model
-- name    : SpikedWishart_FixedDim_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:12.860816+00:00
-- url     : https://prove2.me/theorems/90196992-8448-4a2e-9103-d0ff42e24061
-- title:
--   §1, pp. 1643–1645; (59) — complex Gaussian samples with covariance UΣU*, S = (1/M)Σ y_k y_k*, largest eigenvalue λ₁
-- statement:
--   This file fixes the sample model of Baik, Ben Arous and Péché.
--
--   1. A **standard complex Gaussian** is a random variable $g = a + ib$ on $\mathbb C$ whose real and imaginary parts $a, b$ are independent centred real Gaussians of variance $1/2$; thus $\mathbb E\,g = 0$ and $\mathbb E\,|g|^2 = 1$.
--   2. The **sample law** on $\mathbb C^{M\times N}$ makes the entries $G_{kj}$ ($1\le k\le M$, $1\le j\le N$) independent standard complex Gaussians. It is a probability measure.
--   3. Given a unitary $N\times N$ matrix $U$ and positive population eigenvalues $\ell_1,\dots,\ell_N$, the $k$-th **sample** is
--   $$\vec y_k = U\,\operatorname{diag}\big(\sqrt{\ell_1},\dots,\sqrt{\ell_N}\big)\,\vec g_k,\qquad \vec g_k = (G_{k1},\dots,G_{kN})^{\mathsf T},$$
--   a mean-zero complex Gaussian vector with covariance $\Sigma = U\operatorname{diag}(\ell_1,\dots,\ell_N)U^*$. Every positive definite Hermitian $\Sigma$ has this form.
--   4. The **sample covariance matrix** is
--   $$S = \frac1M\sum_{k=1}^M \vec y_k\,\vec y_k^{\,*},$$
--   an $N\times N$ Hermitian matrix, and $\lambda_1$ denotes its **largest eigenvalue**.
--
--   This is the model of the paper's formula (59), $p(S)\propto e^{-M\operatorname{tr}(\Sigma^{-1}S)}(\det S)^{M-N}$, used in every theorem of the paper.
--
--   **Formalization Note** The page's density (1) "with the complex inner product", the normalisation $S = \frac1N XX^*$ on p. 1645 and the centring by the sample mean on p. 1643 are printed slips that contradict (59), (61) and the paper's other exact formulas; the samples are taken mean-zero and uncentred, with $E\,\vec y\vec y^{\,*} = \Sigma$ and factor $1/M$. The largest eigenvalue is the supremum over $i$ of Mathlib's eigenvalues of the Hermitian matrix $S$ (Hermitian-ness is the structural lemma `sampleCov_isHermitian` in this file); it is the maximum eigenvalue whenever $N \ge 1$. The same declarations appear in the other missions of this series under their own sub-namespaces.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), pp. 1643–1645, §1, §1.1; p. 1655, (59)

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Model

namespace SpikedWishart.FixedDim

open MeasureTheory ProbabilityTheory Matrix

/-- The standard circularly-symmetric complex Gaussian law on `ℂ`: real and imaginary parts are
independent `N(0, 1/2)`, so `E|g|² = 1`. -/
noncomputable def stdComplexGaussian : Measure ℂ :=
  ((gaussianReal 0 (1 / 2 : NNReal)).prod (gaussianReal 0 (1 / 2 : NNReal))).map
    (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ))

instance stdComplexGaussian.instIsProbabilityMeasure :
    IsProbabilityMeasure stdComplexGaussian :=
  Measure.isProbabilityMeasure_map (Complex.measurableEquivRealProd.symm.measurable.aemeasurable)

/-- The law of the `M × N` array `G` of i.i.d. standard complex Gaussians: `G k j` is the `j`-th
standard coordinate of the `k`-th sample. -/
noncomputable def sampleLaw (M N : ℕ) : Measure (Fin M → Fin N → ℂ) :=
  Measure.pi fun _ => Measure.pi fun _ => stdComplexGaussian

instance sampleLaw.instIsProbabilityMeasure (M N : ℕ) : IsProbabilityMeasure (sampleLaw M N) := by
  unfold sampleLaw; infer_instance

theorem sampleCov_isHermitian (M : ℕ) {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N → ℝ)
    (G : Fin M → Fin N → ℂ) : (SpikedWishart.Separated.sampleCov M U ℓ G).IsHermitian := by
  unfold SpikedWishart.Separated.sampleCov Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp [Matrix.conjTranspose_vecMulVec, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]

end SpikedWishart.FixedDim


