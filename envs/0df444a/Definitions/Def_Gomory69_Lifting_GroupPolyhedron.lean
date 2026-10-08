-- Prove2me | Definitions.Def_Gomory69_Lifting_GroupPolyhedron
-- name    : Gomory69_Lifting_GroupPolyhedron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:58.656064+00:00
-- url     : https://prove2.me/theorems/6096fea5-931d-46fa-92c6-2fb54e93bf98
-- title:
--   The group equation (5), the master polyhedron P(G, g0) and its faces (pp. 457–458, 468–469, 474)
-- statement:
--   Let $\mathcal G$ be a finite Abelian group, written additively, with zero $\bar 0$, and let $\mathcal G^+=\mathcal G-\{\bar 0\}$. For $g_0\in\mathcal G$, the **group equation** (5) asks for nonnegative integers $t(g)$, $g\in\mathcal G^+$, with
--
--   $$\sum_{g\in\mathcal G^+} t(g)\cdot g = g_0 .$$
--
--   Its set of solutions is $T=T(\mathcal G,g_0)\subseteq\mathbb N^{\mathcal G^+}$; when $g_0=\bar 0$, the zero solution is excluded, as the paper specifies on p. 474. Each $t\in T$ is a point of the real space $\mathbb R^{\mathcal G^+}$ ("T-space", of dimension $n'=|\mathcal G|-1$), and the **master polyhedron** $P(\mathcal G,g_0)$ is the convex hull of $T$ in that space.
--
--   An inequality $\sum_{g\in\mathcal G^+}\pi(g)t(g)\ge\pi_0$, written $(\pi,\pi_0)$, is a **face** of $P(\mathcal G,g_0)$ when
--
--   1. $\pi\neq 0$;
--   2. (i)′ $\pi\cdot t\ge\pi_0$ for every $t\in T$;
--   3. (ii)′ the points of $T$ on the hyperplane $\pi\cdot t=\pi_0$ generate it: every point $x$ with $\pi\cdot x=\pi_0$ is a weighted sum, with total weight $1$, of points $t\in T$ with $\pi\cdot t=\pi_0$.
--
--   A face in this sense is a facet, an $(n'-1)$-dimensional face; Gomory says "face" for facet throughout. Finally, a coefficient vector $\pi$ on $\mathcal G^+$ is extended to all of $\mathcal G$ by the convention $\pi(\bar 0)=0$.
--
--   These objects are defined once for an arbitrary finite Abelian group, so that they can be used for a group $\mathcal G$ and a quotient $\mathcal H$ of it at the same time.
--
--   **Formalization Note** Vectors are indexed by the subtype `Plus G = {g // g ≠ 0}`, so $\bar 0$ has no coordinate and the dimension of T-space is $|\mathcal G|-1$. "Generate" is read as: the affine span of the tight points of $T$ equals the hyperplane $\{x:\pi\cdot x=\pi_0\}$. Faces are defined through $T$, conditions (i)′ and (ii)′ of p. 469, which the page states are equivalent to (i) and (ii) for $P$. The page's "$\pi_0$ a scalar $\ge 0$" is not built into the definition, because THEOREM 6 proves it. The Lean definition excludes $t=0$ for every $g_0$; for $g_0\ne\bar 0$ the group equation already excludes it. `ext π` is the extension with $\pi(\bar 0)=0$.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), pp. 457–458 (group equation (5), P(G, N, g0)), pp. 468–469 (faces, (11), (i)′ and (ii)′), p. 474 ((12), P(G, g0)), p. 486 (π′(0̄) = 0)

import Mathlib

namespace Gomory69.Lifting

/-- `𝒢⁺ = 𝒢 − 0̄`, the nonzero elements of the group; the coordinates of T-space for
`P(𝒢, g₀) = P(𝒢, 𝒢⁺, g₀)`. -/
abbrev Plus (G : Type*) [AddCommGroup G] : Type _ := {g : G // g ≠ 0}

/-- The set `T` of nonnegative integer solutions of the group equation (5),
`∑_{g ∈ 𝒢⁺} t(g) · g = g₀`. The zero solution is excluded, as stipulated for
`g₀ = 0̄` in the footnote on p. 474; for `g₀ ≠ 0̄` this exclusion is automatic. -/
def T (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (g₀ : G) :
    Set (Plus G → ℕ) :=
  {t | (∑ g : Plus G, t g • (g : G) = g₀) ∧ t ≠ 0}

/-- A nonnegative integer vector viewed as a point of real T-space. -/
def castVec {G : Type*} [AddCommGroup G] (t : Plus G → ℕ) : Plus G → ℝ :=
  fun g => (t g : ℝ)

/-- The master polyhedron `P(𝒢, g₀)`: the convex hull of `T` in real T-space. -/
def P (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (g₀ : G) :
    Set (Plus G → ℝ) :=
  convexHull ℝ (castVec '' T G g₀)

/-- `(π, π₀)` is a face (facet) of `P(𝒢, g₀)`: `π ≠ 0`, (i)′ `π · t ≥ π₀` for every `t ∈ T`,
and (ii)′ the points of `T` on the hyperplane `π · t = π₀` generate it, i.e. their affine span is
the whole hyperplane. -/
def IsFace (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (g₀ : G)
    (π : Plus G → ℝ) (π₀ : ℝ) : Prop :=
  π ≠ 0 ∧ (∀ t ∈ T G g₀, π₀ ≤ π ⬝ᵥ castVec t) ∧
    ((affineSpan ℝ (castVec '' {t | t ∈ T G g₀ ∧ π ⬝ᵥ castVec t = π₀}) : Set (Plus G → ℝ)) =
      {x | π ⬝ᵥ x = π₀})

/-- Extension of a coefficient vector on `𝒢⁺` to all of `𝒢` by the convention `π(0̄) = 0`. -/
def ext {G : Type*} [AddCommGroup G] [DecidableEq G] (π : Plus G → ℝ) : G → ℝ :=
  fun g => if hg : g = 0 then 0 else π ⟨g, hg⟩

end Gomory69.Lifting


