-- Prove2me | Definitions.Def_LRTempElim_Supplement_Norms
-- name    : LRTempElim_Supplement_Norms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:36:20.637915+00:00
-- url     : https://prove2.me/theorems/8de8a7bb-448a-48cc-92fb-9ed242a49a54
-- title:
--   Euclidean, Frobenius and spectral norms $\|\cdot\|_2$, $\|\cdot\|_F$, $\|\cdot\|_{\mathrm{op}}$
-- statement:
--   For a vector $x\in\mathbb R^k$ and a matrix $A\in\mathbb R^{k\times k}$,
--   $$
--   \|x\|_2=\Big(\sum_i x_i^2\Big)^{1/2},\qquad \|A\|_F=\Big(\sum_{i,j}A_{ij}^2\Big)^{1/2},\qquad \|A\|_{\mathrm{op}}=\sup_{\|x\|_2\le1}\|Ax\|_2 .
--   $$
--
--   These are the norms in which the constants (13) of Theorem 3 and the perturbation sizes $\epsilon_G,\epsilon_d$ of Theorem B.22 are measured.
--
--   **Formalization Note** Vectors are `Fin k → ℝ`, whose default Lean norm is the sup norm, so the Euclidean norm is written out. The spectral norm is the operator norm of the matrix acting on `EuclideanSpace ℝ (Fin k)`.
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), eq. (13), p.8 (pdf p.10); Theorem B.22, p.38 (pdf p.40)

import Mathlib

open Matrix

namespace LRTempElim

namespace Supplement

/-!
# Vector and matrix norms used by Theorems 3 and B.22

W. Chen, Y. Wu, J. Yang, D. Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic
Temporal Elimination*, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee65139…),
eq. (13), p.8 (pdf p.10) and Theorem B.22, p.38 (pdf p.40).

The paper writes `∥·∥₂` for the Euclidean norm of a vector, `∥·∥_F` for the Frobenius norm and
`∥·∥_op` for the spectral (operator) norm of a matrix.

**Formalization Note.** Vectors of `ℝᵏ` are `Fin k → ℝ`. Mathlib's default norm on `Fin k → ℝ` is
the sup norm, so the Euclidean norm is written out explicitly. The operator norm is the norm of the
matrix as a continuous linear endomorphism of Euclidean space `EuclideanSpace ℝ (Fin k)`.
-/

/-- The Euclidean norm `∥x∥₂ = (∑ᵢ xᵢ²)^{1/2}` of a vector of `ℝᵏ`. -/
noncomputable def eNorm {k : ℕ} (x : Fin k → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- The Frobenius norm `∥A∥_F = (∑ᵢⱼ Aᵢⱼ²)^{1/2}` of a `k × k` matrix. -/
noncomputable def frobNorm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- The spectral norm `∥A∥_op = sup_{∥x∥₂ ≤ 1} ∥Ax∥₂` of a `k × k` matrix, i.e. the operator norm
of `A` acting on Euclidean space. -/
noncomputable def opNorm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) A‖

end Supplement

end LRTempElim


