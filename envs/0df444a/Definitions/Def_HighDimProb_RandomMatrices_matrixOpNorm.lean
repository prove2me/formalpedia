-- Prove2me | Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
-- name    : HighDimProb_RandomMatrices_matrixOpNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:20:23.549145+00:00
-- url     : https://prove2.me/theorems/c97b3dde-21e9-4625-abf1-ebba1623d895
-- title:
--   The operator (spectral) norm of a real matrix
-- statement:
--   The **operator norm** (also called the spectral norm) of an $m \times n$ real matrix $A$,
--   §4.1.2: viewing $A$ as a linear map $\ell_2^n \to \ell_2^m$,
--
--   $$
--   \|A\| \;:=\; \max_{x \in S^{n-1}} \|Ax\|_2 .
--   $$
--
--   It equals the largest singular value of $A$, and controls how much $A$ can distort
--   Euclidean distances.
--
--   **Formalization Note** $A$ is represented as a linear map between the finite-dimensional
--   Euclidean spaces $\mathbb R^n$ and $\mathbb R^m$ (`Matrix.toEuclideanLin`); every linear map
--   between finite-dimensional normed spaces is automatically continuous
--   (`LinearMap.toContinuousLinearMap`), and `matrixOpNorm` is that continuous linear map's
--   operator norm, as supplied by Mathlib for `E →L[ℝ] F`. This coincides with the book's
--   `maxₓ∈Sⁿ⁻¹ ‖Ax‖₂`. Used consistently for the operator norm throughout this mission
--   (Exercise 4.4.3(a) and the goal, Theorem 4.4.5).
-- source:
--   Vershynin, High-Dimensional Probability (2018), §4.1.2, p. 77 (PDF p. 85)

import Mathlib

namespace HighDimProb.RandomMatrices

/-- The operator (spectral) norm of an `m × n` real matrix, Vershynin, *High-Dimensional
Probability* (2018), §4.1.2, p. 77: `‖A‖ := ‖A : ℓⁿ₂ → ℓᵐ₂‖ = maxₓ∈Sⁿ⁻¹ ‖Ax‖₂`. `A` acts as a
continuous linear map between the finite-dimensional Euclidean spaces `EuclideanSpace ℝ (Fin n)`
and `EuclideanSpace ℝ (Fin m)` (every linear map between finite-dimensional normed spaces is
automatically continuous, `LinearMap.toContinuousLinearMap`), and `matrixOpNorm` is its
`ContinuousLinearMap` operator norm, which for a finite-dimensional domain agrees with the
book's `maxₓ∈Sⁿ⁻¹ ‖Ax‖₂` (the sup over the unit ball of a continuous linear map is attained on
the sphere by linearity, and is attained at all since the unit ball is compact). -/
noncomputable def matrixOpNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))‖

end HighDimProb.RandomMatrices


