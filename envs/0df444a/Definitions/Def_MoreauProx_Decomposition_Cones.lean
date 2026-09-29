-- Prove2me | Definitions.Def_MoreauProx_Decomposition_Cones
-- name    : MoreauProx_Decomposition_Cones
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:09:54.780979+00:00
-- url     : https://prove2.me/theorems/4fb4d5ca-2205-45db-81c4-b381fa89c836
-- title:
--   Closed convex cones, polar cones and nearest-point projections in a real Hilbert space
-- statement:
--   Let $H$ be a real Hilbert space with inner product $(x\mid y)$.
--
--   1. A **closed convex cone** (with vertex $0$) is a nonempty, closed, convex set $P \subseteq H$ such that $t x \in P$ for every $x \in P$ and every real $t \ge 0$.
--   2. The **polar cone** of $P$ is
--   $$ P^{\circ} = \{\, y \in H : (x \mid y) \le 0 \text{ for all } x \in P \,\}. $$
--   3. A point $x$ is a **projection of $z$ on a set $C$** when $x \in C$ and $\|z - x\| \le \|z - u\|$ for every $u \in C$, i.e. $x$ is a point of $C$ nearest to $z$.
--
--   These are the objects of Moreau's cone decomposition (Corollaire 4.b), the special case of his decomposition theorem where $f$ is the indicator function of a cone.
--
--   **Formalization Note** The polar cone uses the sign $\le 0$, as in the paper; it is the negative of Mathlib's `innerDual`. The paper writes $x = \mathrm{proj}_C z$ for the nearest point; `IsProj C z x` is the predicate "x is a nearest point of C to z", which for a nonempty closed convex set in a Hilbert space characterizes $\mathrm{proj}_C z$ since that point exists and is unique.
-- source:
--   Moreau, Proximité et dualité dans un espace hilbertien, Bull. Soc. Math. France 93 (1965), p. 281, §4.b; p. 279, 3.d (projection)

import Mathlib

namespace MoreauProx.Decomposition

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A nonempty closed convex cone with vertex `0` (Moreau 1965, 4.b, p. 281). -/
def IsClosedConvexCone (P : Set H) : Prop :=
  P.Nonempty ∧ IsClosed P ∧ Convex ℝ P ∧ ∀ x ∈ P, ∀ t : ℝ, 0 ≤ t → t • x ∈ P

/-- The polar cone `Q = {y ∈ H : (x | y) ≤ 0 for all x ∈ P}` (Moreau 1965, 4.b, p. 281).
Note the sign: this is the negative of Mathlib's `innerDual`. -/
def polarCone (P : Set H) : Set H :=
  {y | ∀ x ∈ P, ⟪x, y⟫_ℝ ≤ 0}

/-- `x` is a projection of `z` on `C`: a point of `C` nearest to `z` (Moreau 1965, 3.d,
p. 279). For a nonempty closed convex `C` in a Hilbert space it is unique, and
`IsProj C z x` is exactly `x = proj_C z`. -/
def IsProj (C : Set H) (z x : H) : Prop :=
  x ∈ C ∧ ∀ u ∈ C, ‖z - x‖ ≤ ‖z - u‖

end MoreauProx.Decomposition


