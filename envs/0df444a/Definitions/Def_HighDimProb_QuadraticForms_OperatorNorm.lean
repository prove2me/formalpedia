-- Prove2me | Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm
-- name    : HighDimProb_QuadraticForms_OperatorNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:26:40.129194+00:00
-- url     : https://prove2.me/theorems/7c1c238a-cf32-4d02-aeef-c8318aec305c
-- title:
--   The operator (spectral) norm of a real matrix
-- statement:
--   This is the **operator norm** (also called the spectral norm) of a real $n \times n$
--   matrix, used throughout Vershynin's *High-Dimensional Probability*, Section 4.1 and
--   Chapter 6.
--
--   For a matrix $A \in \mathbb R^{n \times n}$, viewed as a linear map on Euclidean space
--   $\mathbb R^n$,
--
--   $$
--   \|A\| \;:=\; \sup_{x \in \mathbb R^n,\, \|x\|_2 = 1} \|Ax\|_2,
--   $$
--
--   the largest factor by which $A$ can stretch a unit vector; equivalently, the largest
--   singular value of $A$. It appears in the Hanson-Wright inequality (Theorem 6.2.1) as the
--   scale controlling the heavier, sub-exponential part of the tail of a quadratic form
--   $X^\top A X$.
--
--   **Formalization Note** Defined by identifying $A$ with the continuous linear
--   endomorphism it induces on `EuclideanSpace ℝ (Fin n)` via Mathlib's
--   `Matrix.toEuclideanCLM`, and taking that map's operator norm — the ordinary
--   `ContinuousLinearMap` norm, which carries no instance-diamond risk. This is
--   definitionally the supremum above once `Matrix.toEuclideanCLM` is unfolded, and avoids
--   committing `Matrix (Fin n) (Fin n) ℝ` itself to Mathlib's scoped `Matrix.Norms.L2Operator`
--   norm instance, which would conflict with the Frobenius norm instance used alongside it in
--   this mission.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Section 4.1.2, p. 77 (PDF p. 85)

import Mathlib

namespace HighDimProb.QuadraticForms

/-- The operator (spectral) norm of a real `n × n` matrix `A`, `‖A‖ := sup_{‖x‖₂ = 1} ‖Ax‖₂`, as
used in Vershynin, *High-Dimensional Probability* (2018), Section 4.1 and throughout Chapter 6.
Defined by identifying `A` with the continuous linear endomorphism it induces on Euclidean
space `EuclideanSpace ℝ (Fin n)` (`Matrix.toEuclideanCLM`) and taking that map's operator norm,
which is the standard Mathlib `ContinuousLinearMap` norm and carries no instance-diamond risk,
unlike Mathlib's scoped `Matrix.Norms.L2Operator` norm instance on `Matrix (Fin n) (Fin n) ℝ`
itself. -/
noncomputable def opNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A‖

end HighDimProb.QuadraticForms


