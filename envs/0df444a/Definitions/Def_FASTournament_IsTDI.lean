-- Prove2me | Definitions.Def_FASTournament_IsTDI
-- name    : FASTournament_IsTDI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:30:22.328701+00:00
-- url     : https://prove2.me/theorems/c7cd72ec-179d-4f47-9519-90d9354d8ef7
-- title:
--   Totally dual integral (TDI) system $Ax\ge b,\ x\ge 0$
-- statement:
--   Let $A$ be an integral matrix with rows indexed by a finite set $I$ and columns by a finite set $K$, and let $b\in\mathbb Q^I$. The system $Ax\ge b,\ x\ge 0$ is **totally dual integral (TDI)** if for every integral vector $w\in\mathbb Z^K$ for which the optimum of
--   $$
--   \min\{w^Tx : Ax\ge b,\ x\ge 0\}=\max\{y^Tb : y^TA\le w^T,\ y\ge 0\}
--   $$
--   is finite, the maximum has an integral optimal solution $y$.
--
--   **Formalization Note** "The optimum is finite" is: the primal LP over $\mathbb R$ is feasible and its objective is bounded below; the conclusion asks for an integral $y\ge 0$ with $y^TA\le w^T$ whose value $y^Tb$ is at least that of every real dual-feasible vector. The paper's definition (p.2) quantifies over nonnegative integral $w$; for the nonnegative matrices the paper uses, a cost with a negative entry makes the primal infeasible or unbounded, so the notions coincide.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2

import Mathlib

namespace FASTournament

/-- **Totally dual integral (TDI) system `Ax ≥ b, x ≥ 0`.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.2: the system is TDI if, in the LP-duality equation
`min {wᵀx : Ax ≥ b, x ≥ 0} = max {yᵀb : yᵀA ≤ wᵀ, y ≥ 0}`, the maximum has an integral optimal
solution for every integral `w` for which the optimum is finite.

For every integral cost `w` such that the primal LP `min {wᵀx : Ax ≥ b, x ≥ 0}` is feasible and
bounded below, there is an integral `y ≥ 0` with `yᵀA ≤ wᵀ` whose objective `yᵀb` is at least
that of every real dual-feasible vector.

**Formalization Note.** `A` is an integral matrix with finite row index `ι` and column index
`κ`, `b` is rational, and the LPs are over `ℝ`. The quantifier is over all integral `w` (the
standard notion of Edmonds–Giles and Schrijver); the paper writes "nonnegative integral w", which
gives the same notion for the nonnegative matrices used in the paper, since then a cost with a
negative entry makes the primal unbounded or infeasible. By LP duality a finite primal optimum
means the dual maximum exists and is attained. -/
def IsTDI {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℤ) (b : ι → ℚ) : Prop :=
  ∀ w : κ → ℤ,
    ((∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧ ∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j) ∧
      BddBelow ((fun x : κ → ℝ => ∑ j, (w j : ℝ) * x j) ''
        {x | (∀ j, 0 ≤ x j) ∧ ∀ i, (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * x j})) →
    ∃ y : ι → ℤ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, y i * A i j ≤ w j) ∧
      ∀ y' : ι → ℝ, (∀ i, 0 ≤ y' i) → (∀ j, ∑ i, y' i * (A i j : ℝ) ≤ (w j : ℝ)) →
        ∑ i, y' i * (b i : ℝ) ≤ ∑ i, (y i : ℝ) * (b i : ℝ)

end FASTournament


