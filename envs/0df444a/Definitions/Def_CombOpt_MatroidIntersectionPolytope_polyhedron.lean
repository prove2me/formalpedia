-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_polyhedron
-- name    : CombOpt_MatroidIntersectionPolytope_polyhedron
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:39:53.564428+00:00
-- url     : https://prove2.me/theorems/d60113aa-5caf-49eb-9430-f2befffae2d7
-- title:
--   The polyhedron $\{x : Ax\le b\}$ of a rational system
-- statement:
--   For a rational matrix $A\in\mathbb Q^{m\times n}$ and a rational vector $b\in\mathbb Q^m$, the **polyhedron** of the system $Ax\le b$ is
--
--   $$
--   \{x\in\mathbb R^n : \textstyle\sum_j A_{ij}x_j\le b_i \text{ for every row } i\}.
--   $$
--
--   Polyhedra defined by rational systems are the **rational polyhedra** of §6.4.
--
--   **Formalization Note** Rows and columns are indexed by arbitrary finite types; the entries of $A$ and $b$ are rationals, read as reals.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 203 (PDF p. 211); §6.4, pp. 218–219 (PDF pp. 226–227)

import Mathlib

namespace CombOpt.MatroidIntersectionPolytope

/-- **The polyhedron `{x : Ax ≤ b}`** of a rational linear system.
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 203 (PDF p. 211) ("A polyhedron is the solution set of a finite system of
linear inequalities") and §6.4, pp. 218–219 (PDF pp. 226–227) (rational polyhedra: "polyhedra
that can be defined by rational linear systems").

`polyhedron A b` is the set of `x ∈ ℝ^n` with `Σ_j A_{ij} x_j ≤ b_i` for every row `i`.

**Formalization Note.** Rows and columns are indexed by arbitrary finite types `m`, `n` (the book
uses `{1, …, m}` and `{1, …, n}`, or `S` for matroid systems); the entries of `A` and `b` are
rationals cast to `ℝ`. -/
def polyhedron {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) (b : m → ℚ) :
    Set (n → ℝ) :=
  {x | ∀ i, ∑ j, (A i j : ℝ) * x j ≤ (b i : ℝ)}

end CombOpt.MatroidIntersectionPolytope


