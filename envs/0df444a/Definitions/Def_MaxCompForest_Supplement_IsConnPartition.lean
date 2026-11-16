-- Prove2me | Definitions.Def_MaxCompForest_Supplement_IsConnPartition
-- name    : MaxCompForest_Supplement_IsConnPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:13:26.223251+00:00
-- url     : https://prove2.me/theorems/24ebfca0-c6a5-4da3-99b7-a0256e484e38
-- title:
--   Partition into connected blocks
-- statement:
--   A partition $Q$ of the vertex set of a graph $G$ has **connected blocks** if every block $B\in Q$ induces a connected subgraph $G[B]$ of $G$. Connected blocks are the ones a graph-signal practitioner can interpret as regions of the graph; Theorems 5.3 and J.1 show that on graphs excluding a fixed minor they lose only a constant factor.
--
--   **Formalization Note** Connectivity of the induced subgraph of the underlying simple graph; blocks are nonempty.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 5.3, p.30 (PDF p.32); Theorem J.1, p.59 (PDF p.61)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- **A partition into connected blocks**: every block induces a connected subgraph of the original graph.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 5.3, p.30; Theorem J.1 ("nonempty connected original-graph blocks"), p.59.

**Formalization Note.** Connectivity is that of the induced subgraph of the underlying simple graph of the
multigraph; blocks of a `Finpartition` are nonempty. -/
def IsConnPartition (G : WGraph V E) (Q : Finpartition (Finset.univ : Finset V)) : Prop :=
  ∀ B ∈ Q.parts, (G.toSimpleGraph.induce (B : Set V)).Connected

end MaxCompForest.Supplement


