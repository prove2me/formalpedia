-- Prove2me | Definitions.Def_Gomory69_SpecialGroups_GroupPolyhedron
-- name    : Gomory69_SpecialGroups_GroupPolyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:58:33.882817+00:00
-- url     : https://prove2.me/theorems/963b3ea7-c8da-4ec6-9668-18c7fd9c4001
-- title:
--   The group equation (12), the master polyhedron P(G, g0), irreducible solutions and independent group elements (pp. 459, 474–475, 504)
-- statement:
--   Let $\mathcal G$ be a finite Abelian group, written additively, with zero element $\bar 0$, and let $\mathcal G^+ = \mathcal G \setminus \{\bar 0\}$. A point of **T-space** is a vector $t = (t(g))_{g \in \mathcal G^+}$ with one coordinate for each nonzero group element.
--
--   1. **The group equation.** For $g_0 \in \mathcal G$, a nonnegative integer vector $t$ solves the group equation (12) if
--   $$\sum_{g \in \mathcal G^+} t(g)\cdot g = g_0 ,$$
--   where $t(g)\cdot g$ is the $t(g)$-fold sum of $g$. When $g_0 = \bar 0$ the solution $t = 0$ is excluded.
--   2. **The master polyhedron.** $P(\mathcal G, g_0)$ is the convex hull, in the real space $\mathbb R^{\mathcal G^+}$ of dimension $|\mathcal G| - 1$, of the nonnegative integer solutions of the group equation. Its **vertices** are its extreme points.
--   3. **Irreducibility.** A nonnegative integer vector $t$ is **irreducible** if for all integer vectors $r, s$ with $0 \le r \le t$ and $0 \le s \le t$ componentwise,
--   $$\sum_{g} s(g)\cdot g = \sum_{g} r(g)\cdot g \quad\Longrightarrow\quad r = s .$$
--   4. **Support.** For a vector $t$, $T = \{g \in \mathcal G^+ : t(g) > 0\}$ is the set of group elements on which $t$ is positive.
--   5. **Independence.** A finite set $S$ of group elements is **independent** if for all integers $(s_g)_{g \in S}$, $\sum_{g \in S} s_g g = \bar 0$ implies $s_g g = \bar 0$ for every $g \in S$.
--   6. **Order hypothesis.** For a natural number $p$, every nonzero element of $\mathcal G$ has order $p$. For $p = 2$ these are the groups $\mathcal G_2, \mathcal G_{2,2}, \mathcal G_{2,2,2}, \ldots$, for $p = 3$ the groups $\mathcal G_3, \mathcal G_{3,3}, \ldots$.
--
--   These objects are shared by every statement of the mission: THEOREM 23 compares irreducible solutions with the vertices of $P(\mathcal G, g_0)$, and its proof passes through the independence of the support.
--
--   **Formalization Note** T-space vectors are functions on the subtype `{g : G // g ≠ 0}`; integer solutions are $\mathbb N$-valued and cast to $\mathbb R$ by `toReal`. The vertices of $P(\mathcal G, g_0)$ are `Set.extremePoints ℝ (masterPolyhedron g₀)`. The integer vectors $r, s$ of the irreducibility condition are $\mathbb N$-valued, which is the same as integers between $0$ and $t$. The support is a `Finset G`. The order hypothesis reads the page's "all elements of $\mathcal G$ are of order $p$" as "all nonzero elements": the zero element has order 1.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 457 (group equation (5)), p. 459 (irreducibility), pp. 474–475 (P(G, g0), (12), footnote of p. 474), p. 504 (independent group elements; groups with all elements of order 2 or 3)

import Mathlib

namespace Gomory69.SpecialGroups

/-!
Gomory, *Some polyhedra related to combinatorial problems*, Linear Algebra Appl. 2 (1969):
the group equation (5) and (12) (pp. 457, 475), the master polyhedron `P(𝒢, g₀)` (pp. 474–475,
with the footnote of p. 474), irreducibility (p. 459), independent group elements (p. 504), and the
groups all of whose nonzero elements have one order `p` (p. 504).

The finite Abelian group `𝒢` is written additively. A point of T-space is a vector indexed by
`𝒢⁺ = 𝒢 − 0̄`, the subtype `{g : G // g ≠ 0}`.
-/

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The left-hand side of the group equation (12), p. 475: `Σ_{g ∈ 𝒢⁺} t(g) · g`, for a
nonnegative integer vector `t` indexed by the nonzero group elements. -/
def groupSum (t : {g : G // g ≠ 0} → ℕ) : G :=
  ∑ g, t g • (g : G)

/-- The set of nonnegative integer solutions of the group equation (12),
`Σ_{g ∈ 𝒢⁺} t(g) · g = g₀` (p. 475). For `g₀ = 0̄` the solution `t = 0` is excluded, as in the
footnote of p. 474. -/
def solutionSet (g₀ : G) : Set ({g : G // g ≠ 0} → ℕ) :=
  {t | groupSum t = g₀ ∧ (g₀ = 0 → t ≠ 0)}

/-- A nonnegative integer vector of T-space viewed as a real vector. -/
def toReal (t : {g : G // g ≠ 0} → ℕ) : {g : G // g ≠ 0} → ℝ :=
  fun g => (t g : ℝ)

/-- The master polyhedron `P(𝒢, g₀)` (pp. 474–475): the convex hull, in the real
`(|𝒢| − 1)`-dimensional T-space, of the nonnegative integer solutions of (12). Its vertices are its
extreme points, `Set.extremePoints ℝ (masterPolyhedron g₀)`. -/
def masterPolyhedron (g₀ : G) : Set ({g : G // g ≠ 0} → ℝ) :=
  convexHull ℝ (toReal '' solutionSet g₀)

/-- Irreducibility (p. 459): a nonnegative integer vector `t` is irreducible if for all nonnegative
integer vectors `r, s` with `0 ≤ r ≤ t`, `0 ≤ s ≤ t` (componentwise),
`Σ s(g) · g = Σ r(g) · g` implies `r = s`. -/
def IsIrreducible (t : {g : G // g ≠ 0} → ℕ) : Prop :=
  ∀ r s : {g : G // g ≠ 0} → ℕ, r ≤ t → s ≤ t → groupSum s = groupSum r → r = s

/-- The set of group elements `g` with `t(g) > 0` (called `T` on pp. 505–506). -/
def support (t : {g : G // g ≠ 0} → ℕ) : Finset G :=
  (Finset.univ.filter (fun g => 0 < t g)).map (Function.Embedding.subtype _)

/-- Independent group elements (p. 504): a set `S` of group elements is independent if, for all
integers `s_g`, `Σ_{g ∈ S} s_g g = 0̄` implies `s_g g = 0̄` for every `g ∈ S`. -/
def IsIndependent (S : Finset G) : Prop :=
  ∀ s : G → ℤ, ∑ g ∈ S, s g • g = 0 → ∀ g ∈ S, s g • g = 0

end Gomory69.SpecialGroups

namespace Gomory69.SpecialGroups

/-- The hypothesis of §3F (p. 504) for a fixed `p`: every nonzero element of `𝒢` has order `p`
(the zero element has order `1`). With `p = 2` these are the groups `𝒢₂, 𝒢₂,₂, …`; with `p = 3` the
groups `𝒢₃, 𝒢₃,₃, …`. -/
def AllNonzeroOfOrder (G : Type*) [AddCommGroup G] (p : ℕ) : Prop :=
  ∀ g : G, g ≠ 0 → addOrderOf g = p

end Gomory69.SpecialGroups


