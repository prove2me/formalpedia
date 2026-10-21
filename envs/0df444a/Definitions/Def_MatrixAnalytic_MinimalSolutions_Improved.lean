-- Prove2me | Definitions.Def_MatrixAnalytic_MinimalSolutions_Improved
-- name    : MatrixAnalytic_MinimalSolutions_Improved
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:25.7962+00:00
-- url     : https://prove2.me/theorems/ae6db138-1a8a-4db2-b393-10e69e533a5f
-- title:
--   The sequences Ḡ(k), Ū(k) of the improved algorithm (8.29)–(8.31)
-- statement:
--   Let $\iota$ be a finite set of phases and $A_0, A_1, A_2$ real $\iota\times\iota$ matrices. The sequences $\{\bar G(k)\}$ and $\{\bar U(k)\}$ of Section 8.3 are defined by
--
--   $$\bar G(0) = I,\qquad \bar U(k) = A_1 + A_0\bar G(k-1),\qquad \bar G(k) = (I - \bar U(k))^{-1}A_2 \quad\text{for } k\ge1. \tag{8.29–8.31}$$
--
--   They start the linear progression iteration from the stochastic matrix $I$ instead of $0$.
--
--   **Formalization Note** The inverse is the ordinary matrix inverse of a finite real matrix, which Lean assigns a default value when the matrix is singular; that $I - \bar U(k)$ is nonsingular is a conclusion of Theorem 8.3.1, not an assumption. $\bar U(k)$ is meant for $k\ge1$ only.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 179, Eqs. (8.29)–(8.31)

import Mathlib

namespace MatrixAnalytic.MinimalSolutions

noncomputable section

/-!
The sequences `{Ū(k)}` and `{Ḡ(k)}` of the improved algorithm, Theorem 8.3.1 of Latouche &
Ramaswami (p. 179), for a QBD with finitely many phases:
`Ḡ(0) = I` (8.29), `Ū(k) = A₁ + A₀Ḡ(k − 1)` (8.30), `Ḡ(k) = (I − Ū(k))⁻¹A₂` for `k ≥ 1` (8.31).
The inverse is Mathlib's matrix inverse, which is a junk value for a singular matrix; that
`I − Ū(k)` is nonsingular is part of what Theorem 8.3.1 asserts, never assumed here.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Ḡ(k)`: `Ḡ(0) = I` and `Ḡ(k + 1) = (I − (A₁ + A₀Ḡ(k)))⁻¹A₂`, i.e. (8.29)–(8.31). -/
def Gbar (A₀ A₁ A₂ : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 1
  | k + 1 => (1 - (A₁ + A₀ * Gbar A₀ A₁ A₂ k))⁻¹ * A₂

/-- `Ū(k) = A₁ + A₀Ḡ(k − 1)` (8.30). Meant for `k ≥ 1`. -/
def Ubar (A₀ A₁ A₂ : Matrix ι ι ℝ) (k : ℕ) : Matrix ι ι ℝ :=
  A₁ + A₀ * Gbar A₀ A₁ A₂ (k - 1)

end

end MatrixAnalytic.MinimalSolutions


