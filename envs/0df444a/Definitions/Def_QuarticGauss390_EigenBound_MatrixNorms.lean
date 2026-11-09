-- Prove2me | Definitions.Def_QuarticGauss390_EigenBound_MatrixNorms
-- name    : QuarticGauss390_EigenBound_MatrixNorms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:05.366808+00:00
-- url     : https://prove2.me/theorems/96034007-b326-4fa9-968f-bda7a37ccd84
-- title:
--   Operator, Frobenius and nuclear norms of matrices
-- statement:
--   For a square matrix $A$ over $\mathbb R$ or $\mathbb C$, the **operator norm** $\|A\|_{\mathrm{op}}$ is its norm as a linear map on the Euclidean space (the spectral norm, the largest singular value). For a real matrix, the **Frobenius norm** is
--   $$\|A\|_F=\Big(\sum_{i,j}A_{ij}^2\Big)^{1/2},$$
--   and for a real symmetric matrix the **nuclear norm** $\|A\|_*$ is the sum of the absolute values of its eigenvalues.
--
--   These are the norms of the paper's §2 conventions (p.5) and of Lemma 3.2 (p.11); they are used for coefficient matrices, moment matrices and Hamiltonians.
--
--   **Formalization Note.** The operator norm is the norm of `Matrix.toEuclideanCLM A`, not Mathlib's default entrywise matrix norm. The nuclear norm takes a proof that $A$ is Hermitian, which for real matrices means symmetric.
-- source:
--   Ojas Parekh, Improved classical optimization of fermionic Hamiltonians beyond Gaussian states, STOC 2027 submission #390 (October 2026), source.pdf SHA-256 9018757e184cce1091160d8b5847294a0e6c16cc09386b1f2b6bb000f7542101, p.5, §2 preamble (norm conventions); p.11 (nuclear norm)

import Mathlib

open Matrix

namespace QuarticGauss390.EigenBound

/-- Operator (spectral) norm `‖A‖_op`: the norm of `A` as a linear map on the Euclidean space
`𝕜^ι`. -/
noncomputable def opNorm {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι) A‖

/-- Frobenius norm `‖A‖_F = √(∑_{i,j} A_ij²)` of a real matrix. -/
noncomputable def frobNorm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- p.11: nuclear norm `‖A‖_*` of a real symmetric matrix, the sum of the absolute values of
its eigenvalues. -/
noncomputable def nuclearNorm {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

end QuarticGauss390.EigenBound


