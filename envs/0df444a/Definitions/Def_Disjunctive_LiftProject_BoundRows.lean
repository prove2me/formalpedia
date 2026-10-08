-- Prove2me | Definitions.Def_Disjunctive_LiftProject_BoundRows
-- name    : Disjunctive_LiftProject_BoundRows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T22:00:28.028346+00:00
-- url     : https://prove2.me/theorems/9e1b1e67-ccb7-46fd-9a73-4f94b0e59639
-- title:
--   Mixed 0-1 LP relaxation with the bound rows folded in (Chapter 6)
-- statement:
--   The system $\tilde A x \ge \tilde b$ (rows indexed by a finite type $M$) is the LP relaxation of a mixed 0-1 program $\min\{cx : Ax \ge b,\ x \ge 0,\ x_j \in \{0,1\},\ j \in N'\}$ with the bound constraints folded in, as in Balas, *Disjunctive Programming*, §6: the inequalities $x \ge 0$ and $x_j \le 1$ ($j \in N'$) are included in $\tilde A x \ge \tilde b$. Concretely, the system contains, for every coordinate $k$, a row $x_k \ge 0$ (row vector $e_k$, right-hand side $0$), and for every $j \in N'$ a row $-x_j \ge -1$ (row vector $-e_j$, right-hand side $-1$).
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §6 (p. 79), Setting of Chapter 6

import Mathlib

namespace Disjunctive.LiftProject

/-- The system `Ãx ≥ b̃` (rows indexed by a finite type `M`) is the LP relaxation of a mixed 0-1
program `min{cx : Ax ≥ b, x ≥ 0, x_j ∈ {0,1}, j ∈ N'}` with the bound constraints folded in, as
in Balas §6 (p. 79): "`P := {x : Ãx ≥ b̃}`, with the inequalities `x ≥ 0` and `x_j ≤ 1`,
`j ∈ N'`, included in `Ãx ≥ b̃`". Concretely, the system contains, for every coordinate `k`, a
row `x_k ≥ 0` (row vector `e_k`, right-hand side `0`), and for every `j ∈ N'` a row `-x_j ≥ -1`
(row vector `-e_j`, right-hand side `-1`). -/
def HasBoundRows {n : ℕ} {M : Type*} (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (Nprime : Finset (Fin n)) : Prop :=
  (∀ k : Fin n, ∃ ρ : M, Atil ρ = Pi.single k 1 ∧ btil ρ = 0) ∧
    ∀ j ∈ Nprime, ∃ ρ : M, Atil ρ = -Pi.single j 1 ∧ btil ρ = -1

end Disjunctive.LiftProject


