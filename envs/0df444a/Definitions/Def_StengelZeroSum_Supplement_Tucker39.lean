-- Prove2me | Definitions.Def_StengelZeroSum_Supplement_Tucker39
-- name    : StengelZeroSum_Supplement_Tucker39
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:26:29.745808+00:00
-- url     : https://prove2.me/theorems/914bbe37-2e3b-566b-b464-d3d744466234
-- title:
--   The statement of Tucker's Theorem (39) for a matrix $A$
-- statement:
--   For a real $m\times n$ matrix $A$, the proposition $\mathrm{Tucker39}(A)$ is (39):
--
--   $$
--   \exists\,y\in\mathbb R^m,\ x\in\mathbb R^n:\quad y^\top A\ge\mathbf 0^\top,\quad x\ge\mathbf 0,\quad Ax=\mathbf 0,\quad x^\top+y^\top A>\mathbf 0^\top .
--   $$
--
--   Vector inequalities hold componentwise; the last condition says $x_j+(y^\top A)_j>0$ for every $j\in[n]$.
--
--   This is a proposition about $A$, not a theorem. Tucker's Theorem asserts it for every real matrix; Theorem 6 derives it from Gordan's Theorem.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Proposition 9, eq. (39), p.15

import Mathlib

open Matrix

namespace StengelZeroSum.Supplement

/-- The statement of **Tucker's Theorem (39)** for a matrix `A ∈ ℝ^{m×n}`, von Stengel,
*Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Proposition 9, eq. (39),
p.15:
`∃ y ∈ ℝ^m, x ∈ ℝ^n : y⊤A ≥ 0⊤, x ≥ 0, Ax = 0, x⊤ + y⊤A > 0⊤`.

**Formalization Note** Vector inequalities are componentwise (p.4); `x⊤ + y⊤A > 0⊤` says every
component `x_j + (y⊤A)_j` is strictly positive, written `∀ j, 0 < x j + (y ᵥ* A) j` (not
Lean's `Pi.lt`). This is a proposition, not a theorem:
`StengelZeroSum.Supplement.tucker_theorem_39` asserts it for every real matrix, and Theorem 6
derives it from Gordan's Theorem. -/
def Tucker39 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ (y : Fin m → ℝ) (x : Fin n → ℝ),
    0 ≤ y ᵥ* A ∧ 0 ≤ x ∧ A *ᵥ x = 0 ∧ ∀ j, 0 < x j + (y ᵥ* A) j

end StengelZeroSum.Supplement


