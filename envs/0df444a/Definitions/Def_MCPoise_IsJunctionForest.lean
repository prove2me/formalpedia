-- Prove2me | Definitions.Def_MCPoise_IsJunctionForest
-- name    : MCPoise_IsJunctionForest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:06.452708+00:00
-- url     : https://prove2.me/theorems/8f6b13b0-3ce7-44e2-aa8b-e0f1966e8b9d
-- title:
--   $(\alpha, \beta)$-junction forest
-- statement:
--   Given an instance and a value $L$, an **$(\alpha, \beta)$-junction forest** is a collection of rooted trees $T_1, \dots, T_M \subseteq G$ with roots $r_1, \dots, r_M$ and collections of demands $D_1, \dots, D_M \subseteq D$ such that
--
--   1. $T_1, \dots, T_M$ are edge-disjoint;
--   2. the union $H = \bigcup_j T_j$ satisfies $\max_{v} \deg_H(v) \le \alpha L$;
--   3. for each $j$ and each $(s_i, t_i) \in D_j$, the tree $T_j$ contains $s_i$-$r_j$ and $t_i$-$r_j$ paths, each of length at most $\beta L$.
--
--   A junction forest replaces the single junction tree of cost-based network design, since a degree objective cannot be averaged over partial solutions.
--
--   **Formalization Note** A tree may have one vertex. $D_j$ is a set of demand indices.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 2, p.6

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_maxDeg

namespace MCPoise

/-- **`(α, β)`-junction forest.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Definition 2, p.6: "a collection of rooted trees T₁, . . . , T_M ⊆ G with roots r₁, . . . , r_M, each
with a collection of terminal pairs D₁, . . . , D_M ⊆ D such that 1. T₁, . . . , T_M are edge-disjoint; 2. Let
H = ∪_{j∈[M]} T_j, then max_{v∈V} deg_H(v) ≤ α · L; 3. For each j ∈ [M], (s_i, t_i) ∈ D_j, there exist paths
s_i-r_j and t_i-r_j paths in T_j, each of length at most β · L."

`L` is a parameter: the page's "optimal solution value" is an instance of it.

**Formalization Note.** A tree is a `G.Subgraph` whose coercion is a Mathlib tree and whose vertices contain
the root, so a one-vertex tree is allowed. `D_j` is a set of demand indices. "Paths in `T_j`" are walks of
`spanningCoe`, which use only edges of `T_j`; a walk of length at most `β L` contains such a path. -/
structure IsJunctionForest (I : Inst) (L α β : ℝ) {M : ℕ} (T : Fin M → I.graph.Subgraph)
    (r : Fin M → Fin I.n) (D : Fin M → Finset (Fin I.k)) : Prop where
  tree : ∀ j, (T j).coe.IsTree
  root_mem : ∀ j, r j ∈ (T j).verts
  edge_disjoint : Pairwise fun j j' => Disjoint (T j).edgeSet (T j').edgeSet
  degree : (maxDeg (⨆ j, (T j).spanningCoe) : ℝ) ≤ α * L
  paths : ∀ j, ∀ i ∈ D j,
    (∃ p : (T j).spanningCoe.Walk (I.s i) (r j), (p.length : ℝ) ≤ β * L) ∧
    (∃ p : (T j).spanningCoe.Walk (I.t i) (r j), (p.length : ℝ) ≤ β * L)

end MCPoise


