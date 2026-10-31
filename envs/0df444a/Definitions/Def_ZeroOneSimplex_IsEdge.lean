-- Prove2me | Definitions.Def_ZeroOneSimplex_IsEdge
-- name    : ZeroOneSimplex_IsEdge
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:16.79985+00:00
-- url     : https://prove2.me/theorems/0a1efd31-35cf-4b5a-9c85-de610390d2f9
-- title:
--   Polytopes, edges, improving neighbors, monotone paths, maximizers
-- statement:
--   Vocabulary for a set $Q\subseteq\mathbb R^n$:
--
--   1. $Q$ is a **polytope** if it is the convex hull of finitely many points.
--   2. Two points $x\ne y$ form an **edge** of $Q$ if the segment $[x,y]$ is a face (an extreme subset) of $Q$; both endpoints are then vertices of $Q$.
--   3. $N_c(x)=\{u : [x,u] \text{ is an edge of } Q,\ c^\top u > c^\top x\}$ is the set of **$c$-improving neighbors** of $x$.
--   4. A **$v$-monotone path** is a sequence of vertices $x^0,\dots,x^k$ of $Q$ in which consecutive vertices form edges and $v^\top x^{i-1} < v^\top x^i$.
--   5. $x$ is a **$c$-maximum** of $Q$ if $x\in Q$ and $c^\top y\le c^\top x$ for all $y\in Q$.
--   6. The **$v$-minimal face** of $Q$ is the set of points of $Q$ minimizing $v^\top x$.
--
--   These are the objects of §3.1 of the paper, used for the 1-skeleton of the feasible region.
--
--   **Formalization Note** The edge predicate is that of the published `Hirsch_model` (`Hirsch.Adj`), restated locally.
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, §1.1, p.6 (edges, N_c(x)); §3.1, p.12 (v-monotone paths); p.15 (face minimized by v)

import Mathlib

set_option autoImplicit false

namespace ZeroOneSimplex

/-- A **polytope** in `ℝⁿ`: the convex hull of finitely many points. -/
def IsPolytope {n : ℕ} (Q : Set (Fin n → ℝ)) : Prop :=
  ∃ S : Finset (Fin n → ℝ), Q = convexHull ℝ (S : Set (Fin n → ℝ))

/-- **Edge** of the 1-skeleton (arXiv:2111.14050v1, pp.6, 12): `x ≠ y` and the segment `[x, y]`
is an extreme subset (a face) of `Q`. Both endpoints are then vertices of `Q`.

**Formalization Note.** This is the adjacency predicate of the published `Hirsch_model`
(`Hirsch.Adj`), restated locally. -/
def IsEdge {n : ℕ} (Q : Set (Fin n → ℝ)) (x y : Fin n → ℝ) : Prop :=
  x ≠ y ∧ IsExtreme ℝ Q (segment ℝ x y)

/-- The set `N_c(x)` of **`c`-improving neighbors** of `x` in `Q` (arXiv:2111.14050v1, p.6):
vertices `u` adjacent to `x` with `cᵀu > cᵀx`. -/
def improvingNbrs {n : ℕ} (Q : Set (Fin n → ℝ)) (c x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {u | IsEdge Q x u ∧ c ⬝ᵥ x < c ⬝ᵥ u}

/-- **`v`-monotone path** (arXiv:2111.14050v1, p.12): vertices `x 0, …, x k` of `Q` with
`(x (i-1), x i)` an edge of `Q` and `vᵀx (i-1) < vᵀx i` for `1 ≤ i ≤ k`. Only the values
`x 0, …, x k` matter. -/
def IsMonotonePath {n : ℕ} (Q : Set (Fin n → ℝ)) (v : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (k : ℕ) : Prop :=
  x 0 ∈ Set.extremePoints ℝ Q ∧
    ∀ i < k, IsEdge Q (x i) (x (i + 1)) ∧ v ⬝ᵥ x i < v ⬝ᵥ x (i + 1)

/-- `x` **maximizes** `c` on `Q` (`x` is a `c`-maximum of `Q`). -/
def IsMaximizer {n : ℕ} (Q : Set (Fin n → ℝ)) (c x : Fin n → ℝ) : Prop :=
  x ∈ Q ∧ ∀ y ∈ Q, c ⬝ᵥ y ≤ c ⬝ᵥ x

/-- The face of `Q` **minimized by `v`** (the `v`-minimal face): the points of `Q` where `vᵀx`
is least (arXiv:2111.14050v1, pp.12–13, 15). -/
def vMinFace {n : ℕ} (Q : Set (Fin n → ℝ)) (v : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ Q ∧ ∀ y ∈ Q, v ⬝ᵥ x ≤ v ⬝ᵥ y}

end ZeroOneSimplex


