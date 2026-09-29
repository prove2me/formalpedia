-- Prove2me | Definitions.Def_ResourceScheduling_Graph_GraphPartition
-- name    : ResourceScheduling_Graph_GraphPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:25:35.40754+00:00
-- url     : https://prove2.me/theorems/327341dc-ce20-4521-906c-629ee4f22aec
-- title:
--   PARTITION INTO TRIANGLES and PARTITION INTO PATHS OF LENGTH 2
-- statement:
--   This module defines the two graph problems from which Theorems 2 and 3 are proved, as the paper states them (after Garey and Johnson, problems GT11 and GT13).
--
--   An instance is a natural number $t$ and a simple graph $G=(V,E)$ with $|V|=3t$.
--
--   1. **PARTITION INTO TRIANGLES**: "Given a graph $G=(V,E)$ with $|V|=3t$, can $V$ be partitioned into $t$ disjoint subsets, each containing three pairwise adjacent vertices?"
--   2. **PARTITION INTO PATHS OF LENGTH 2**: "Given a graph $G=(V,E)$ with $|V|=3t$, can $V$ be partitioned into $t$ disjoint subsets, each containing three vertices, at most two of which are nonadjacent?" The phrase means that at most one of the three pairs in each subset is nonadjacent, i.e. each subset spans at least two edges and so contains a path of length $2$ (Garey and Johnson's GT13). Equivalently, $G$ has a spanning, not necessarily induced, $P_3$-factor.
--
--   A graph is encoded over $\{\mathtt{1},\mathtt{\#}\}$ as $t$ in unary followed by its $3t\times3t$ adjacency matrix row by row ($\mathtt{1}$ for an edge, $\mathtt{\#}$ for a non-edge). The languages of the two problems are the sets of codes of yes-instances.
--
--   **Formalization Note.** $V$ is `Fin (3 * t)`, so $|V|=3t$ is part of every instance. The partition into triangles is a bijection $\mathrm{Fin}\,t\times\mathrm{Fin}\,3\simeq V$ listing the three vertices of each block. The partition into paths reuses the published definition `CubicP3Partition.P3Factor` (module `cubic_p3_partition_models`): a bijection from $\mathrm{Fin}\,b\times\mathrm{Fin}\,3$ onto $V$ such that the first and second, and the second and third, vertices of each block are adjacent; the number of blocks $b$ is then $t$.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, proofs of Theorems 2 and 3 (citing Garey & Johnson [5], problems GT11, GT13)

import Mathlib
import Definitions.Def_ResourceScheduling_Graph_Complexity
import Definitions.Def_cubic_p3_partition_models

/-!
# PARTITION INTO TRIANGLES and PARTITION INTO PATHS OF LENGTH 2

Błażewicz, Lenstra & Rinnooy Kan (1983), p. 15, proofs of Theorems 2 and 3, citing Garey &
Johnson (1979), problems GT11 and GT13. An instance is a graph `G = (V, E)` with `|V| = 3t`;
here `V = Fin (3 * t)`, so `|V| = 3t` is part of the instance.
-/

namespace ResourceScheduling.Graph

/-- An instance of the two graph partition problems: `t` and a graph on `3t` vertices with
decidable adjacency. -/
structure GraphData where
  t : ℕ
  G : SimpleGraph (Fin (3 * t))
  [decAdj : DecidableRel G.Adj]

attribute [instance] GraphData.decAdj

/-- Code of a graph instance: `t` in unary, then the `3t × 3t` adjacency matrix row by row,
`one` for an edge and `sep` for a non-edge. -/
def encGraph (d : GraphData) : List Letter :=
  unary d.t ++
    (List.finRange (3 * d.t)).flatMap fun i =>
      (List.finRange (3 * d.t)).map fun j => if d.G.Adj i j then Letter.one else Letter.sep

/-- PARTITION INTO TRIANGLES: `V` can be partitioned into `t` disjoint subsets, each containing
three pairwise adjacent vertices. The bijection `place` lists the three vertices of each block. -/
def PartitionIntoTriangles {t : ℕ} (G : SimpleGraph (Fin (3 * t))) : Prop :=
  ∃ place : Fin t × Fin 3 ≃ Fin (3 * t),
    ∀ (i : Fin t) (a b : Fin 3), a ≠ b → G.Adj (place (i, a)) (place (i, b))

/-- PARTITION INTO PATHS OF LENGTH 2: `V` can be partitioned into disjoint subsets of three
vertices, each containing at least two of its three possible edges (at most one nonadjacent
pair), i.e. `G` has a (not necessarily induced) `P₃`-factor. -/
def PartitionIntoPathsOfLength2 {t : ℕ} (G : SimpleGraph (Fin (3 * t))) : Prop :=
  Nonempty (CubicP3Partition.P3Factor G)

/-- The language of PARTITION INTO TRIANGLES. -/
def trianglesLang : CookPvsNP.Lang Letter :=
  codeLang (fun d : GraphData => PartitionIntoTriangles d.G) encGraph

/-- The language of PARTITION INTO PATHS OF LENGTH 2. -/
def pathsLang : CookPvsNP.Lang Letter :=
  codeLang (fun d : GraphData => PartitionIntoPathsOfLength2 d.G) encGraph

end ResourceScheduling.Graph


