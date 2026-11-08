-- Prove2me | Definitions.Def_MaxCompForest_spanSub
-- name    : MaxCompForest_spanSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:33:25.573191+00:00
-- url     : https://prove2.me/theorems/a645f38e-9716-4376-9a26-dc40ae691e36
-- title:
--   The spanning subgraph $(V,S)$ of a set of edge labels
-- statement:
--   For a set $S$ of edge labels of $G=(V,E)$, the graph $(V,S)$ on the same vertices, in which two vertices are adjacent when a label of $S$ joins them.
--
--   **Formalization Note** It is a simple graph, used only for connectivity and for components. Forests and trees are defined from it together with the number of labels, so that two parallel labels do not pass as a forest.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), p.1, p.17

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*}

/-- **The spanning subgraph `(V, S)`** of a set `S` of edge labels, as a simple graph on `V`: it records
which vertices the labels of `S` join. Components of `(V, S)` are the blocks of the forest `S`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.1, p.17.

**Formalization Note.** Connectivity and component count are all this graph is used for; the labels
themselves are counted separately in `IsSpanningTree` and `IsForest`, so parallel labels stay distinct. -/
def spanSub (G : WGraph V E) (S : Finset E) : SimpleGraph V :=
  SimpleGraph.fromRel fun a b => ∃ e ∈ S, G.head e = a ∧ G.tail e = b

end MaxCompForest


