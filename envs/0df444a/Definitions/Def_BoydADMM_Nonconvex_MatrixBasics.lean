-- Prove2me | Definitions.Def_BoydADMM_Nonconvex_MatrixBasics
-- name    : BoydADMM_Nonconvex_MatrixBasics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:56.169721+00:00
-- url     : https://prove2.me/theorems/10a3dd68-73bb-4114-91d0-8ad8fc549388
-- title:
--   Symmetric real matrices and squared Frobenius norm
-- statement:
--   For an $n\times n$ real matrix $X$, symmetry means $X_{ij}=X_{ji}$ for every pair of indices. The squared Frobenius norm is
--
--   $$\|X\|_F^2=\sum_{i=1}^n\sum_{j=1}^n X_{ij}^2.$$
--
--   The diagonal matrix $\operatorname{diag}(d)$ has entries $d_i$ on its diagonal and zero elsewhere. These are the finite-dimensional matrix conventions used for the factor-model X-update.
--
--   **Formalization Note** The index type is `Fin n`; thus $i=1,\ldots,n$ in the book corresponds to indices $0,\ldots,n-1$ in Lean. The finite sum is the square of the book's Frobenius norm, so it works directly in the squared-loss formulas.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 75, §9.1.2

import Mathlib

namespace BoydADMM.Nonconvex

/-- Real square matrices, used for the symmetric factor model of §9.1.2. -/
abbrev SqMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Symmetry of a real square matrix. -/
def IsSymmetric {n : ℕ} (X : SqMat n) : Prop :=
  ∀ i j, X i j = X j i

/-- The square of the Frobenius norm, as the sum of squares of all ordered entries. -/
def frobSq {n : ℕ} (X : SqMat n) : ℝ :=
  ∑ i, ∑ j, (X i j) ^ 2

/-- The diagonal matrix with diagonal `d`. -/
def diag {n : ℕ} (d : Fin n → ℝ) : SqMat n :=
  Matrix.diagonal d

end BoydADMM.Nonconvex


