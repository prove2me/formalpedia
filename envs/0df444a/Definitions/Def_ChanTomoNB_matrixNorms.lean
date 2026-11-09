-- Prove2me | Definitions.Def_ChanTomoNB_matrixNorms
-- name    : ChanTomoNB_matrixNorms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:13.367578+00:00
-- url     : https://prove2.me/theorems/f129e61c-4a96-41d7-8d3b-0793a16df493
-- title:
--   Operator norm $\|\cdot\|_{\mathrm{op}}$, Frobenius norm $\|\cdot\|_F$ and smallest singular value $\sigma_{\min}$
-- statement:
--   For a complex matrix $M\in\mathbb C^{m\times k}$:
--
--   1. $\|M\|_{\mathrm{op}}$ is the operator norm of $M$ as a map between Euclidean spaces (its largest singular value);
--   2. $\|M\|_F=\big(\sum_{i,j}|M_{ij}|^2\big)^{1/2}$ is the Frobenius norm;
--   3. $\sigma_{\min}(M)=\lambda_{\min}(M^\dagger M)^{1/2}$ is the smallest singular value.
--
--   These norms measure the Gaussian matrices and the range displacements of the construction.
--
--   **Formalization Note** $\sigma_{\min}$ is undefined for $k=0$; there the value is $0$, and every statement using it assumes $k\ge1$.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Lemmas 5.5, 5.7 and 5.9, pp.27–30

import Mathlib

open Matrix

namespace ChanTomoNB

/-- The operator norm `‖M‖_op` of `M : ℂ^n → ℂ^m` (the largest singular value): the norm of the
linear map `EuclideanSpace ℂ n → EuclideanSpace ℂ m` that `M` represents. Chen, Oufkir,
*Quantum channel tomography: optimal bounds in the near-boundary regime*, arXiv:2611.03639v1,
§5 (Lemmas 5.5, 5.7, 5.9, pp.27–30).

**Formalization Note.** This is Mathlib's `L2Operator` matrix norm, written through
`Matrix.toEuclideanLin` so that no scoped norm instance is needed on `Matrix`. -/
noncomputable def opNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖

/-- The Frobenius norm `‖M‖_F = (∑_{i,j} |M_{ij}|²)^{1/2}` (arXiv:2611.03639v1, Lemma 5.7,
p.29). -/
noncomputable def frobNorm {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖M i j‖ ^ 2)

/-- The smallest singular value `σ_min(M) = λ_min(M†M)^{1/2}` of `M ∈ ℂ^{m×k}`
(arXiv:2611.03639v1, Lemma 5.5, p.27).

**Formalization Note.** The minimum of the (nonnegative) eigenvalues of the Hermitian matrix
`M†M`, written as a `⨅` over `Fin k`. For `k ≥ 1` this is the paper's `σ_min`; for `k = 0` the
paper's quantity is undefined and the value here is `0`, so every statement using it assumes
`1 ≤ k`. -/
noncomputable def sigmaMin {m : Type} [Fintype m] {k : ℕ} (M : Matrix m (Fin k) ℂ) : ℝ :=
  Real.sqrt (⨅ i, (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues i)

end ChanTomoNB


