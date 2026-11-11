-- Prove2me | Definitions.Def_LewensteinGreedy_Competitive_Geometry
-- name    : LewensteinGreedy_Competitive_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:31:02.531106+00:00
-- url     : https://prove2.me/theorems/e45f47c3-b7a4-46d6-bf5c-9832c7078710
-- title:
--   Arboreal satisfaction and column projection (Definition 2.1, §6.2)
-- statement:
--   A point $(v,t)$ has a key (column) coordinate $v$ and a time (row) coordinate $t$. **Definition 2.1.** A finite point set $P$ is *arboreally satisfied* if every pair of points of $P$ on different rows and different columns has a third point of $P$ in their closed axis-aligned rectangle; pairs on one row or one column are already satisfied, and a point on the rectangle's boundary counts as a witness.
--
--   For a map $\pi$ of key columns, $\pi(P)=\{(\pi(x),t):(x,t)\in P\}$.
--
--   **Formalization Note.** Points are `ℝ × ℝ` (key, time), which contains every integer point set of the source. `ArboreallySatisfied P`: for $p,q\in P$ with $p_1\ne q_1$ and $p_2\ne q_2$ there is $z\in P$, $z\ne p$, $z\ne q$, with $\min(p_1,q_1)\le z_1\le\max(p_1,q_1)$ and $\min(p_2,q_2)\le z_2\le\max(p_2,q_2)$. `projectColumns π P` is the image of $P$ under $(x,t)\mapsto(\pi(x),t)$.
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Definition 2.1 and §6.2, printed p. 4–5, 40 / PDF 5–6, 41

import Mathlib

set_option autoImplicit false

noncomputable section

namespace LewensteinGreedy.Competitive

/-!
# Arboreal satisfaction and column projection

Lewenstein, *Greedy BST is O(log log n)-Competitive*, supplied 2026 artifact (SHA-256
04ac49f6…), Definition 2.1, printed pp.4–5 / PDF 5–6, and §6.2, printed p.40 / PDF 41.

A point is `(key, time)`. A finite point set `P` is arboreally satisfied if every two points of
`P` on different columns and different rows have a third point of `P` (distinct from both) in
their closed axis-parallel rectangle; boundary points count. Pairs on one row or one column impose
nothing. Coordinates are real, so every integer point set of the source is covered.

`projectColumns π P = {(π x, t) : (x, t) ∈ P}`.
-/

/-- Definition 2.1 (arboreal satisfaction), closed-rectangle version. -/
def ArboreallySatisfied (P : Finset (ℝ × ℝ)) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p.1 ≠ q.1 → p.2 ≠ q.2 →
    ∃ z ∈ P, z ≠ p ∧ z ≠ q ∧
      min p.1 q.1 ≤ z.1 ∧ z.1 ≤ max p.1 q.1 ∧
      min p.2 q.2 ≤ z.2 ∧ z.2 ≤ max p.2 q.2

/-- The image of a point set under a map of its key columns. -/
def projectColumns (π : ℝ → ℝ) (P : Finset (ℝ × ℝ)) : Finset (ℝ × ℝ) :=
  P.image fun p => (π p.1, p.2)

end LewensteinGreedy.Competitive


