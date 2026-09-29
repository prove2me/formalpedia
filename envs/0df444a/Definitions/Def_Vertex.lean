-- Prove2me | Definitions.Def_Vertex
-- name    : Vertex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-04T13:53:36.744052+00:00
-- url     : https://prove2.me/theorems/8dd43a80-4963-42fb-86d6-129a0ed4bed1
-- title:
--   Vertex and extreme point of a polyhedron
-- statement:
--   **(Definition 2.7)** Let $P$ be a polyhedron. A vector $x \in P$ is a *vertex* of $P$ if there exists some $c$ such that
--
--   $$c'x < c'y$$
--
--   for all $y$ satisfying $y \in P$ and $y \ne x$.
--
--   In other words, $x$ is a vertex of $P$ if and only if $P$ is on one side of a hyperplane (the hyperplane $\{y \mid c'y = c'x\}$) which meets $P$ only at the point $x$.
--
--   *Encoding:* (The companion Definition 2.6 — $x \in P$ is an extreme point of $P$ if we cannot find two vectors $y, z \in P$, both different from $x$, and a scalar $\lambda \in [0,1]$, such that $x = \lambda y + (1-\lambda)z$ — is exactly Mathlib's `Set.extremePoints` and is deliberately NOT minted here.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 2.7, p. 47 (Definition 2.6, p. 46)

import Definitions.Def_Polyhedron

/-!
Vertices of polyhedra.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, **Definition 2.7 (p. 47)**: "Let `P` be a
polyhedron. A vector `x ∈ P` is a *vertex* of `P` if there exists some `c`
such that `c'x < c'y` for all `y` satisfying `y ∈ P` and `y ≠ x`."

The companion geometric notion, the *extreme point* (**Definition 2.6,
p. 46**: `x ∈ P` that cannot be written as `λy + (1−λ)z` with
`y, z ∈ P` both different from `x` and `λ ∈ [0,1]`) is NOT re-minted:
it is Mathlib's `Set.extremePoints ℝ P` (the open-segment formulation,
equivalent to the book's).
-/

open Matrix

namespace LinearOptimization

/-- **B&T Definition 2.7 (p. 47).** `x` is a vertex of `P` if `x ∈ P` and
`x` is the unique minimizer of some linear cost over `P`: there exists `c`
with `c'x < c'y` for every `y ∈ P` other than `x`. -/
def IsVertex {n : ℕ} (P : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  x ∈ P ∧ ∃ c : Fin n → ℝ, ∀ y ∈ P, y ≠ x → c ⬝ᵥ x < c ⬝ᵥ y

end LinearOptimization


