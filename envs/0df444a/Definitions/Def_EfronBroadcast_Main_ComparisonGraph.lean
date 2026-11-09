-- Prove2me | Definitions.Def_EfronBroadcast_Main_ComparisonGraph
-- name    : EfronBroadcast_Main_ComparisonGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:45.997933+00:00
-- url     : https://prove2.me/theorems/bd0cd4fc-0113-4730-95f2-2a84643aed9b
-- title:
--   Sparse comparison-graph property
-- statement:
--   Let $G$ be a finite simple graph on the value indices $[n]$, and let $1\le c\le n$. Its degree at $v$ is the number of distinct neighbors of $v$. The comparison property is
--
--   $$
--   X\cap Y=\varnothing,\quad c|X|\ge n,\quad c|Y|\ge n
--   \quad\Longrightarrow\quad
--   \exists x\in X,\ y\in Y:\ \{x,y\}\in E(G).
--   $$
--
--   The multiplicative threshold is exactly $|X|,|Y|\ge n/c$ for positive $c$. No graph-existence or sparsity conclusion is assumed here. This predicate supplies the non-degree part of Lemma 2; finite simple graphs themselves are Mathlib's existing general object.
-- source:
--   Yuval Efron, Jovan Komatovic, Ling Ren, Byzantine Broadcast in Õ(n²) Communication, STOC 2027 submission #526 (October 2026), p. 2, PDF p. 3, Lemma 2; pinned local source.pdf, SHA256 626a479d5227c34ed2d6343fdc7113666962d88d8b482e8a2be02db9f8028a0f

import Mathlib
set_option autoImplicit false

namespace EfronBroadcast.Main

/-- Degree of a finite simple graph, explicitly counting its neighbors. -/
noncomputable def comparisonDegree {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

/-- The comparison property of Lemma 2. Multiplying by `c` expresses the real
threshold `|X|, |Y| ≥ n/c` exactly, without truncated natural division. -/
def ComparisonProperty {n : ℕ} (c : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ X Y : Finset (Fin n), Disjoint X Y → n ≤ c * X.card → n ≤ c * Y.card →
    ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y

end EfronBroadcast.Main


