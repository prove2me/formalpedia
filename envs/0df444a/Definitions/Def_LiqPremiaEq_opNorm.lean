-- Prove2me | Definitions.Def_LiqPremiaEq_opNorm
-- name    : LiqPremiaEq_opNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:01:02.218968+00:00
-- url     : https://prove2.me/theorems/32325df8-bd09-41a9-92ca-7997d0f2bc8a
-- title:
--   Frobenius norm $\|\cdot\|$ and operator norm $\|\cdot\|_{op}$ of real vectors and matrices
-- statement:
--   For a vector $v\in\mathbb R^m$ and a matrix $A\in\mathbb R^{m\times n}$ the paper writes $\|v\|$ and $\|A\|$ for the **Frobenius** (Euclidean) norm, the square root of the sum of squared entries:
--
--   $$\|v\|=\Big(\sum_i v_i^2\Big)^{1/2},\qquad \|A\|=\Big(\sum_{i,j}A_{ij}^2\Big)^{1/2}.$$
--
--   The **operator norm** of $A$ is
--
--   $$\|A\|_{op}=\sup\{\|Ab\| : b\in\mathbb R^{n},\ \|b\|=1\},$$
--
--   the norm of $A$ as a linear map between Euclidean spaces.
--
--   These are the two norms in which all estimates of the paper are stated, e.g. the Gronwall bound (7.13).
--
--   **Formalization Note** Written as explicit functions `frobVec`, `frob`, `opNorm`; `opNorm A` is the norm of the continuous linear map `Matrix.toEuclideanLin A` (Mathlib's scoped `Matrix.Norms.L2Operator` value). No norm instance is opened, so Mathlib's entrywise sup norm never enters.
-- source:
--   Muhle-Karbe–Shi–Yang, An Equilibrium Model for the Cross-Section of Liquidity Premia, arXiv:2011.13625v1, Notation, p.3; Definition 7.2, p.16

import Mathlib

open Matrix

namespace LiqPremiaEq

/-- The Frobenius (Euclidean) norm of a vector, `‖v‖ = (∑ᵢ vᵢ²)^{1/2}`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Notation, p.3: "for any vector or matrix, ‖·‖ is the
Frobenius norm, i.e., the square root of the sum of squared entries".

**Formalization Note** Defined explicitly so that it never collides with Mathlib's default sup
norm on `ι → ℝ`. -/
noncomputable def frobVec {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The Frobenius norm of a matrix, `‖A‖ = (∑ᵢⱼ Aᵢⱼ²)^{1/2}`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Notation, p.3.

**Formalization Note** Defined explicitly; Mathlib's default matrix norm (not an instance) would
be the entrywise sup norm. -/
noncomputable def frob {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- The operator norm `‖A‖op = sup{‖Ab‖ : ‖b‖ = 1}` with Euclidean norms on both sides, i.e. the
`ℓ²` operator norm of `A` viewed as a linear map `EuclideanSpace ℝ n → EuclideanSpace ℝ m`.
Muhle-Karbe–Shi–Yang, arXiv:2011.13625v1, Definition 7.2, p.16.

**Formalization Note** This is the value of Mathlib's scoped `Matrix.Norms.L2Operator` norm
(`Matrix.l2_opNorm_def`), written as an explicit function so that no norm instance is opened. -/
noncomputable def opNorm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (𝕜 := ℝ) A)‖

end LiqPremiaEq


