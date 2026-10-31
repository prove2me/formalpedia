-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_system87Matrix
-- name    : CombOpt_MatroidIntersectionPolytope_system87Matrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:56.057663+00:00
-- url     : https://prove2.me/theorems/19400b6c-ec9b-4bea-adff-1b4ad1a0df0b
-- title:
--   Constraint matrix of (8.7) as a system $Ax\le b$
-- statement:
--   The system (8.7) has one inequality $x(A)\le r_1(A)$ and one inequality $x(A)\le r_2(A)$ for each $A\subseteq S$, and one inequality $x_e\ge0$ for each $e\in S$. Written as $Ax\le b$, its rows are indexed by two copies of the subsets of $S$ and one copy of $S$:
--
--   1. the row $(1,A)$ and the row $(2,A)$ have coefficient $1$ on $e\in A$ and $0$ elsewhere;
--   2. the row $e$ has coefficient $-1$ on $e$ and $0$ elsewhere (the inequality $-x_e\le0$).
--
--   This is the system to which total dual integrality (Theorem 8.23) refers.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.5, (8.7), pp. 297–298 (PDF pp. 304–305)

import Mathlib

namespace CombOpt.MatroidIntersectionPolytope

/-- **The constraint matrix of (8.7)**, written as a system `Ax ≤ b`.
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.5, (8.7), pp. 297–298 (PDF pp. 304–305).

Rows are indexed by `(Finset S ⊕ Finset S) ⊕ S`: the row `inl (inl A)` is `x(A) ≤ r₁(A)`, the row
`inl (inr A)` is `x(A) ≤ r₂(A)` (both with the characteristic vector of `A` as coefficients), and
the row `inr e` is `−x_e ≤ 0` (the constraint `x_e ≥ 0`).

**Formalization Note.** (8.7) has one inequality per pair `(i, A)` with `i ∈ {1, 2}` and
`A ⊆ S` (including `A = ∅`), plus the `|S|` nonnegativity rows; this matrix lists exactly those
rows, as the book's system is written. -/
def system87Matrix {S : Type*} [Fintype S] [DecidableEq S] :
    Matrix ((Finset S ⊕ Finset S) ⊕ S) S ℚ :=
  fun i e =>
    match i with
    | Sum.inl (Sum.inl A) => if e ∈ A then 1 else 0
    | Sum.inl (Sum.inr A) => if e ∈ A then 1 else 0
    | Sum.inr f => if e = f then -1 else 0

end CombOpt.MatroidIntersectionPolytope


