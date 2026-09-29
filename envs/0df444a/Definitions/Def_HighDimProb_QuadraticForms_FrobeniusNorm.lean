-- Prove2me | Definitions.Def_HighDimProb_QuadraticForms_FrobeniusNorm
-- name    : HighDimProb_QuadraticForms_FrobeniusNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:25:54.10237+00:00
-- url     : https://prove2.me/theorems/ae2b60fd-6194-451c-bf7c-b04411332988
-- title:
--   The Frobenius norm of a real matrix
-- statement:
--   This is the **Frobenius norm** of a real $n \times n$ matrix, the standard measure of a
--   matrix's overall size used throughout Vershynin's *High-Dimensional Probability*, Eq.
--   (4.1) and Chapter 6.
--
--   For a matrix $A = (A_{ij})_{i,j=1}^n \in \mathbb R^{n \times n}$,
--
--   $$
--   \|A\|_F \;:=\; \Bigl(\sum_{i=1}^n \sum_{j=1}^n A_{ij}^2\Bigr)^{1/2}.
--   $$
--
--   Equivalently, $\|A\|_F$ is the Euclidean ($\ell^2$) norm of $A$ viewed as a vector of
--   $n^2$ real entries. It appears in the Hanson-Wright inequality (Theorem 6.2.1) as the
--   scale controlling the sub-gaussian part of the tail of a quadratic form $X^\top A X$.
--
--   **Formalization Note** Defined directly as the square root of the sum of squared
--   entries, matching the book's Eq. (4.1) verbatim, rather than through Mathlib's
--   `Matrix.Norms.Frobenius` scoped `Norm` instance on `Matrix (Fin n) (Fin n) ℝ` — that
--   instance is deliberately not a global default in Mathlib (to avoid a diamond with the
--   operator-norm instance this mission also uses), so this development names the two norms
--   as separate functions, `frobeniusNorm` and `opNorm`, rather than overloading `‖·‖`.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Section 4.1.3, p. 78 (PDF p. 86)

import Mathlib

namespace HighDimProb.QuadraticForms

/-- The Frobenius norm of a real `n × n` matrix `A`, `‖A‖_F := (∑ᵢⱼ Aᵢⱼ²)^{1/2}`, as used in
Vershynin, *High-Dimensional Probability* (2018), Section 4.1 (Eq. (4.1)) and throughout
Chapter 6. Stated directly as the square root of the sum of squared entries, matching the
book's Eq. (4.1), rather than through Mathlib's `Matrix.Norms.Frobenius` scoped norm instance,
so that this file does not commit the whole mission to a single, global choice of `Norm` on
`Matrix (Fin n) (Fin n) ℝ` (Mathlib deliberately withholds these matrix norms from the default
instance to avoid a diamond with the operator norm used in `OperatorNorm.lean`). -/
noncomputable def frobeniusNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)

end HighDimProb.QuadraticForms


