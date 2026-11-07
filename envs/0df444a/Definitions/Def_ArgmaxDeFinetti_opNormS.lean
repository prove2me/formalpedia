-- Prove2me | Definitions.Def_ArgmaxDeFinetti_opNormS
-- name    : ArgmaxDeFinetti_opNormS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:16.390426+00:00
-- url     : https://prove2.me/theorems/860ed131-f4fc-4d6a-aa16-2b4573979cdc
-- title:
--   Singular values and the operator norm $\|X\|_\infty$
-- statement:
--   For a complex matrix $X$, the singular values $s_j(X)$ are the square roots of the eigenvalues of $X^\dagger X$, and the Schatten $\infty$-norm (operator norm) is
--   $$
--   \|X\|_\infty=\max_j s_j(X).
--   $$
--   It bounds the witnesses in the trace-norm duality (2.9), (2.11), (3.5) and appears in the final estimate (3.18).
--
--   **Formalization Note** For a rectangular $m\times n$ matrix the list has $n$ entries (the singular values padded by zeros when $n>m$), which changes no maximum and no sum; the maximum is written as a supremum of the finite list, equal to $0$ for a matrix without columns.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18 (Schatten norms)

import Mathlib

open Matrix

namespace ArgmaxDeFinetti

/-- The singular values `s_j(X) = √λ_j(X†X)` of a complex matrix `X`, indexed by the columns,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18.

**Formalization Note** For an `m × n` matrix this lists the `n` eigenvalue square roots of `X†X`, which are
the singular values padded with zeros when `n > m`; the padding changes no maximum and no sum. -/
noncomputable def singularValues {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : n → ℝ :=
  fun j => Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues j)

/-- The Schatten `∞`-norm (operator norm) `∥X∥_∞ = max_j s_j(X)`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2, p.18.

**Formalization Note** The maximum of the finitely many singular values is written as `sSup` of their range;
for a matrix with no columns the range is empty and the value is `0`, the norm of the zero map. -/
noncomputable def opNormS {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (X : Matrix m n ℂ) : ℝ :=
  sSup (Set.range (singularValues X))

end ArgmaxDeFinetti


