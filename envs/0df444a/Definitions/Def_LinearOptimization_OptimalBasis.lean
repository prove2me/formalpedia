-- Prove2me | Definitions.Def_LinearOptimization_OptimalBasis
-- name    : LinearOptimization_OptimalBasis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T17:22:34.092095+00:00
-- url     : https://prove2.me/theorems/f7404b2e-7bb9-403e-a04a-f75d78349175
-- title:
--   Optimal basis
-- statement:
--   **(Definition 3.3)** A basis matrix $B$ is said to be *optimal* if:
--
--   - **(a)** $B^{-1}b \ge 0$, and
--   - **(b)** $\bar{c}' = c' - c_B'B^{-1}A \ge 0'$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 3.3, p. 87

import Definitions.Def_LinearOptimization_ReducedCost

/-!
Optimal bases.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, **Definition 3.3 (p. 87)**: "A basis matrix `B` is
said to be *optimal* if: (a) `B⁻¹b ≥ 0`, and (b) `c̄' = c' − c_B'B⁻¹A ≥ 0'`."

"Basis matrix" presupposes linearly independent basic columns (§2.3,
pp. 54–55), so `IsStdBasis A B` is part of the predicate; it also
discharges the invertibility guard for `B⁻¹` (Lean's `Matrix.inv`).
Per the book (p. 87): if an optimal basis is found, the corresponding
basic solution is feasible, satisfies the optimality conditions, and is
therefore optimal.
-/

open Matrix

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, Definition 3.3 (p. 87).** The basis `B` is optimal (for the
standard-form problem `min c'x, Ax = b, x ≥ 0`) if it is a genuine basis
(`IsStdBasis A B`), the associated basic solution is feasible
(`B⁻¹b ≥ 0`), and every reduced cost is nonnegative. -/
def IsOptimalBasis {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (B : Fin m ↪ Fin n) : Prop :=
  IsStdBasis A B ∧
  0 ≤ (basisMatrix A B)⁻¹.mulVec b ∧
  ∀ j, 0 ≤ reducedCost A c B j

end LinearOptimization


