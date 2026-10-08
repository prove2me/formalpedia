-- Prove2me | Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
-- name    : Gomory69_Asymptotic_GroupPolyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:28:31.117021+00:00
-- url     : https://prove2.me/theorems/e0ed4fef-f086-48aa-b949-363b6798845f
-- title:
--   The group equation (5), the polyhedron P(G, N, g0) and irreducible points (pp. 457–459)
-- statement:
--   Let $\mathcal G$ be an Abelian group, written additively, and let $\mathcal N\subseteq\mathcal G$ be a finite set of group elements; a point of **$\mathcal N$-space** (or $T$-space) is a real vector $t=(t(g))_{g\in\mathcal N}$. For a right-hand side $g_0\in\mathcal G$, the **group equation** (5) is
--
--   $$\sum_{g\in\mathcal N} t(g)\cdot g = g_0,\qquad t(g)\ \text{nonnegative integers},$$
--
--   where $t(g)\cdot g$ is the $t(g)$-fold sum of $g$. Its set of nonnegative integer solutions is denoted $T$.
--
--   1. The **polyhedron** $P(\mathcal G,\mathcal N,g_0)$ is the convex hull, in the real $n'$-dimensional $T$-space ($n'=|\mathcal N|$), of the nonnegative integer solutions of (5).
--   2. A nonnegative integer vector $t=(t(g))_{g\in\mathcal N}$ is **irreducible** if for all integer vectors $s, r$ the conditions $0\le s(g)\le t(g)$, $0\le r(g)\le t(g)$ for all $g$ and
--   $$\sum_{g\in\mathcal N} s(g)\cdot g=\sum_{g\in\mathcal N} r(g)\cdot g$$
--   imply $r(g)=s(g)$ for all $g\in\mathcal N$.
--
--   These are the basic objects of Gomory's theory of corner (group) polyhedra; the vertices of $P(\mathcal G,\mathcal N,g_0)$ are the candidates for optimal solutions of the group minimization problem.
--
--   **Formalization Note** Vectors are indexed by the elements of $\mathcal N$ (the subtype of the finite set), integer vectors are $\mathbb N$-valued, and `toReal` maps an integer vector to the real point with the same coordinates. The paper defines irreducibility for integer points of $P(\mathcal G,\mathcal N,g_0)$; the definition here applies to any nonnegative integer vector, and the theorems that use it say which vectors they concern. Finiteness of $\mathcal G$ and $0\notin\mathcal N$ are hypotheses of the theorems, not of the definitions.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), pp. 457–459, group equation (5), P(G, N, g0), definition of irreducible (p. 459)

import Mathlib

namespace Gomory69.Asymptotic

/-! Gomory (1969), pp. 457–459: the group equation (5), its solution set `T`, the polyhedron
`P(𝒢, 𝒩, g₀)` and irreducible integer points, for an arbitrary Abelian group `𝒢`
(written additively) and a finite set `𝒩` of group elements. -/

variable {G : Type*} [AddCommGroup G]

/-- The nonnegative integer solutions `t = (t(g))_{g ∈ 𝒩}` of the group equation (5),
`∑_{g ∈ 𝒩} t(g) · g = g₀` (p. 457). -/
def groupSolutions (𝒩 : Finset G) (g₀ : G) : Set (↥𝒩 → ℕ) :=
  {t | ∑ g : ↥𝒩, t g • (g : G) = g₀}

/-- The real point of `𝒩`-space with the same coordinates as the integer vector `t`. -/
def toReal (𝒩 : Finset G) (t : ↥𝒩 → ℕ) : ↥𝒩 → ℝ := fun g => (t g : ℝ)

/-- `P(𝒢, 𝒩, g₀)` (pp. 457–458): the convex hull, in the real `n′`-dimensional `T`-space
`↥𝒩 → ℝ`, of the nonnegative integer solutions of the group equation (5). -/
def groupPolyhedron (𝒩 : Finset G) (g₀ : G) : Set (↥𝒩 → ℝ) :=
  convexHull ℝ (toReal 𝒩 '' groupSolutions 𝒩 g₀)

/-- Irreducibility (p. 459): a nonnegative integer vector `t` is irreducible if for all
integer vectors `s, r` with `0 ≤ s(g) ≤ t(g)`, `0 ≤ r(g) ≤ t(g)` and
`∑ s(g) · g = ∑ r(g) · g` one has `r = s`. -/
def IsIrreducible (𝒩 : Finset G) (t : ↥𝒩 → ℕ) : Prop :=
  ∀ s r : ↥𝒩 → ℤ, (∀ g, 0 ≤ s g ∧ s g ≤ (t g : ℤ)) → (∀ g, 0 ≤ r g ∧ r g ≤ (t g : ℤ)) →
    ∑ g : ↥𝒩, s g • (g : G) = ∑ g : ↥𝒩, r g • (g : G) → r = s

end Gomory69.Asymptotic


