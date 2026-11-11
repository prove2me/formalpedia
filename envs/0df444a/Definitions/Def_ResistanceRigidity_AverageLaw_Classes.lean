-- Prove2me | Definitions.Def_ResistanceRigidity_AverageLaw_Classes
-- name    : ResistanceRigidity_AverageLaw_Classes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:05:31.902199+00:00
-- url     : https://prove2.me/theorems/b42c2a32-231b-452c-bafa-6174f58ecc27
-- title:
--   Equal conductances, complete graphs, stars and connected non-complete triangle-free strongly regular graphs (§3)
-- statement:
--   Let $c$ be the conductance function of a weighted graph on a finite vertex set $V$ with $N$ vertices, and let $G$ be its support graph: $u \sim v$ iff $u \ne v$ and $c(u,v) > 0$ (the published `IncrementalER.adj`). The equality classes of Theorem 3.1 are:
--
--   - **Equal conductances up to scaling** (`EqualConductances`): there is $w > 0$ with $c(u,v) = w$ for every edge $u \sim v$.
--   - **Complete** (`IsComplete`): every two distinct vertices are adjacent.
--   - **Star** (`IsStar`): there is a centre $v$ such that $x \sim y$ holds exactly when $x \ne y$ and one of $x, y$ is $v$; this is $K_{1,N-1}$ (for $N = 3$, the path on three vertices).
--   - **Connected non-complete triangle-free strongly regular** (`IsTriangleFreeSRG`): $G$ is connected, not complete, contains no triangle, and is strongly regular with parameters $(N, k, \lambda, \mu)$ for some $k, \lambda, \mu$: every vertex has $k$ neighbours, every two adjacent vertices have $\lambda$ common neighbours and every two distinct non-adjacent vertices have $\mu$ common neighbours.
--
--   **Formalization Note.** Strong regularity is Mathlib's `SimpleGraph.IsSRGWith`, and triangle-freeness is `CliqueFree 3`. Mathlib's strong regularity also holds for complete and edgeless graphs, so "non-complete" is kept explicitly, as in the paper; triangle-freeness forces $\lambda = 0$ whenever there is an edge.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 6, §3, Theorem 3.1

import Mathlib
import Definitions.Def_IncrementalER_lap

namespace ResistanceRigidity.AverageLaw

/-!
# Equal conductances, complete graphs, stars, triangle-free strongly regular graphs

Tianlang Chen, *A Sharp Rigidity Law for Effective Resistance*, STOC 2027 submission
(manuscript, sha256 3846da8c…1e8b), §3, Theorem 3.1, p. 6.

Each class is a property of the support graph `IncrementalER.adj c` (edges = pairs of
positive conductance). "Up to scaling, equal conductances" means that every edge carries one
common positive conductance `w`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Up to scaling, `c` has equal conductances: some `w > 0` is the conductance of every edge. -/
def EqualConductances (c : V → V → ℝ) : Prop :=
  ∃ w : ℝ, 0 < w ∧ ∀ u v, (IncrementalER.adj c).Adj u v → c u v = w

/-- The support graph is complete: every two distinct vertices are adjacent. -/
def IsComplete (c : V → V → ℝ) : Prop :=
  IncrementalER.adj c = ⊤

/-- The support graph is a star `K_{1,N−1}`: a centre `v` is adjacent to every other vertex and
there are no other edges. -/
def IsStar (c : V → V → ℝ) : Prop :=
  ∃ v : V, ∀ x y : V, (IncrementalER.adj c).Adj x y ↔ x ≠ y ∧ (x = v ∨ y = v)

/-- The support graph is a connected, non-complete, triangle-free strongly regular graph:
connected, not complete, without triangles, and strongly regular with parameters
`(N, k, ℓ, μ)` for some `k, ℓ, μ` (`N = card V`). -/
def IsTriangleFreeSRG (c : V → V → ℝ) : Prop := by
  classical
  exact (IncrementalER.adj c).Connected ∧ IncrementalER.adj c ≠ ⊤ ∧
    (IncrementalER.adj c).CliqueFree 3 ∧
    ∃ k l μ : ℕ, (IncrementalER.adj c).IsSRGWith (Fintype.card V) k l μ

end ResistanceRigidity.AverageLaw


