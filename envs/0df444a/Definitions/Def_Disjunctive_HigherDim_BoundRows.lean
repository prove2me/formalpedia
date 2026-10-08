-- Prove2me | Definitions.Def_Disjunctive_HigherDim_BoundRows
-- name    : Disjunctive_HigherDim_BoundRows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T22:00:27.71213+00:00
-- url     : https://prove2.me/theorems/e0280021-2006-4be8-bba6-107f9781e8a7
-- title:
--   Mixed 0-1 LP relaxation with the bound rows folded in (Chapter 7)
-- statement:
--   The system $Ax \ge b$ is the LP relaxation $\tilde A x \ge \tilde b$ of a mixed 0-1 program with 0-1 index set $N'$, written as in Balas, *Disjunctive Programming*, §7 (p. 91): $K := \{x \in \mathbb R^n : Ax \ge b,\ x \ge 0,\ x_j \le 1,\ j \in N'\} = \{x : \tilde A x \ge \tilde b\}$. Concretely, the system contains, for every coordinate $k$, a row $x_k \ge 0$ (row vector $e_k$, right-hand side $0$), and for every $j \in N'$ a row $-x_j \ge -1$ (row vector $-e_j$, right-hand side $-1$). Every construction of Chapter 7 ($P_j(K)$, the Lovász–Schrijver $N(K)$, the Sherali–Adams $K_t$) multiplies all rows of the system it is given, so under this predicate it multiplies the bound rows as well, as the book does.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §7 (p. 91), Setting of Chapter 7

import Mathlib

namespace Disjunctive.HigherDim

/-- The system `A x ≥ b` is the LP relaxation `Ãx ≥ b̃` of a mixed 0-1 program with 0-1 index
set `N'`, written as in Balas §7 (p. 91): `K := {x ∈ ℝⁿ : Ax ≥ b, x ≥ 0, x_j ≤ 1, j ∈ N'}
= {x : Ãx ≥ b̃}`, i.e. the bound constraints are folded into the system as rows. Concretely, the
system contains, for every coordinate `k`, a row `x_k ≥ 0` (row vector `e_k`, right-hand side
`0`), and for every `j ∈ N'` a row `-x_j ≥ -1` (row vector `-e_j`, right-hand side `-1`).

Every construction of Chapter 7 (`Mj`/`Pj`, the Lovász-Schrijver `MK`/`NOp`, the Sherali-Adams
`IsXt`/`KtSet`) multiplies *all* rows of the system it is given; under this predicate those rows
include the bound rows, exactly as the book multiplies `Ãx ≥ b̃` (not only `Ax ≥ b`). -/
def HasBoundRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) : Prop :=
  (∀ k : Fin n, ∃ i : Fin m, A i = Pi.single k 1 ∧ b i = 0) ∧
    ∀ j ∈ Nprime, ∃ i : Fin m, A i = -Pi.single j 1 ∧ b i = -1

end Disjunctive.HigherDim


