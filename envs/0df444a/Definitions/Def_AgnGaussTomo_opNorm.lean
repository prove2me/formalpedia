-- Prove2me | Definitions.Def_AgnGaussTomo_opNorm
-- name    : AgnGaussTomo_opNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:23.52893+00:00
-- url     : https://prove2.me/theorems/a1371424-bd6d-4ec0-bfd6-02182866182a
-- title:
--   Spectral norm $\|M\|_{\mathrm{op}}$ of a square matrix
-- statement:
--   For a real or complex square matrix $M$, $\|M\|_{\mathrm{op}}=\sup_{x\ne0}\|Mx\|_2/\|x\|_2$ is its operator norm on Euclidean space (its largest singular value).
--
--   It appears as $\|V^{-1}\|_{\mathrm{op}}$, the squeezing parameter that drives the energy dependence of Gaussian tomography, and as the constraint $\|A\|_{\mathrm{op}}<1$ on Bargmann parameters.
--
--   **Formalization Note** The norm of `Matrix.toEuclideanLin M` as a continuous linear map, i.e. Mathlib's `Matrix.Norms.L2Operator` norm, under a name that cannot clash with the Frobenius norm. The index type is any finite type.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Fact 2.4 (p. 11), Lemma 2.8 (p. 13), Theorems 3.4–3.8 (pp. 16–18), Lemma 3.7 (p. 17); PDF = printed + 3

import Mathlib

namespace AgnGaussTomo

/-- **Spectral (ℓ²-operator) norm `‖M‖_op` of a square matrix.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), used in
Fact 2.4 (`‖A‖_op < 1`, printed p. 11), Lemma 2.8 (p. 13), Theorems 3.4–3.8 (pp. 16–18)
(`‖V^{-1}‖_op`), Lemma 3.7 (p. 17).

`opNorm M = sup_{x ≠ 0} ‖Mx‖₂ / ‖x‖₂`, the operator norm of `M` acting on Euclidean space.

**Formalization Note.** Defined as the norm of the continuous linear map `Matrix.toEuclideanLin M`
on `EuclideanSpace 𝕜 ι`; this is Mathlib's `Matrix.Norms.L2Operator` norm (`Matrix.l2_opNorm_def`),
named here so that it never clashes with the Frobenius norm. Works for real and complex matrices. -/
noncomputable def opNorm {𝕜 : Type} [RCLike 𝕜] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖

end AgnGaussTomo


