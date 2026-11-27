-- Prove2me | Definitions.Def_StengelZeroSum_Supplement_Gordan20
-- name    : StengelZeroSum_Supplement_Gordan20
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:26:18.85313+00:00
-- url     : https://prove2.me/theorems/0c881f41-e497-5367-8b83-dd03c8a8b819
-- title:
--   The statement of Gordan's Theorem (20) for a matrix $A$
-- statement:
--   For a real $m\times n$ matrix $A$, the proposition $\mathrm{Gordan20}(A)$ is the equivalence (20):
--
--   $$
--   \nexists\,x\in\mathbb R^n:\ Ax=\mathbf 0,\ x\ge\mathbf 0,\ x\neq\mathbf 0
--   \quad\Longleftrightarrow\quad
--   \exists\,y\in\mathbb R^m:\ y^\top A>\mathbf 0^\top .
--   $$
--
--   Vector inequalities hold componentwise: $x\ge\mathbf 0$ means every $x_j\ge0$, $x\neq\mathbf 0$ means some $x_j\neq0$, and $y^\top A>\mathbf 0^\top$ means every component of $y^\top A$ is strictly positive.
--
--   This is a proposition about $A$, not a theorem. Gordan's Theorem asserts it for every real matrix; Theorem 6 takes it, for all matrices, as its hypothesis.
-- source:
--   von Stengel, Zero-Sum Games and Linear Programming Duality, arXiv:2205.11196v6, Proposition 4, eq. (20), p.9

import Mathlib

open Matrix

namespace StengelZeroSum.Supplement

/-- The statement of **Gordan's Theorem (20)** for a matrix `A ∈ ℝ^{m×n}`, von Stengel,
*Zero-Sum Games and Linear Programming Duality*, arXiv:2205.11196v6, Proposition 4, eq. (20),
p.9:
`∄ x ∈ ℝ^n : Ax = 0, x ≥ 0, x ≠ 0  ⇔  ∃ y ∈ ℝ^m : y⊤A > 0⊤`.

**Formalization Note** Vector inequalities are componentwise (p.4): `x ≥ 0` is `0 ≤ x`
(`Pi.le`), `x ≠ 0` says some component is nonzero, and `y⊤A > 0⊤` says every component of
`y⊤A` is strictly positive, written `∀ j, 0 < (y ᵥ* A) j` (not Lean's `Pi.lt`). This is a
proposition, not a theorem: `StengelZeroSum.Supplement.theorem_20_gordan` asserts it for every
real matrix, and Theorem 6 takes it as a hypothesis. -/
def Gordan20 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (¬ ∃ x : Fin n → ℝ, A *ᵥ x = 0 ∧ 0 ≤ x ∧ x ≠ 0) ↔ ∃ y : Fin m → ℝ, ∀ j, 0 < (y ᵥ* A) j

end StengelZeroSum.Supplement


