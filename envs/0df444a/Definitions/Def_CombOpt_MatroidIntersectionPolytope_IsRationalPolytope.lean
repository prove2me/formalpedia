-- Prove2me | Definitions.Def_CombOpt_MatroidIntersectionPolytope_IsRationalPolytope
-- name    : CombOpt_MatroidIntersectionPolytope_IsRationalPolytope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:49.154995+00:00
-- url     : https://prove2.me/theorems/5f8dfa02-6122-43bb-84f3-cb4a5881aec2
-- title:
--   Rational polytope
-- statement:
--   A set $P\subseteq\mathbb R^n$ is a **rational polytope** if
--
--   1. $P=\{x : Ax\le b\}$ for some rational matrix $A$ with finitely many rows and some rational vector $b$ (a rational polyhedron), and
--   2. there are $l,u\in\mathbb R^n$ with $l\le x\le u$ for every $x\in P$ (a polytope).
--
--   This is the setting of Hoffman's integrality characterization.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.2, p. 204 (PDF p. 212); §6.4, pp. 218–219 (PDF pp. 226–227)

import Mathlib
import Definitions.Def_CombOpt_MatroidIntersectionPolytope_polyhedron

namespace CombOpt.MatroidIntersectionPolytope

/-- **Rational polytope.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.2, p. 204 (PDF p. 212): "a polyhedron P ⊆ ℝⁿ is a polytope if there exist l, u ∈ ℝⁿ
such that l ≤ x ≤ u for all x ∈ P"; §6.4, pp. 218–219 (PDF pp. 226–227): rational polyhedra are
"polyhedra that can be defined by rational linear systems".

`IsRationalPolytope P` holds when `P = {x : Ax ≤ b}` for some rational matrix `A` (finitely many
rows) and rational vector `b`, and there are `l, u ∈ ℝⁿ` with `l ≤ x ≤ u` for all `x ∈ P`.

**Formalization Note.** The coordinates are indexed by an arbitrary finite type `n`; rows by
`Fin k` for some `k`. -/
def IsRationalPolytope {n : Type*} [Fintype n] (P : Set (n → ℝ)) : Prop :=
  (∃ (k : ℕ) (A : Matrix (Fin k) n ℚ) (b : Fin k → ℚ), P = polyhedron A b) ∧
    ∃ l u : n → ℝ, ∀ x ∈ P, l ≤ x ∧ x ≤ u

end CombOpt.MatroidIntersectionPolytope


