-- Prove2me | Definitions.Def_SnarkGen_CycleCover_IsCycleCover
-- name    : SnarkGen_CycleCover_IsCycleCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:55.139536+00:00
-- url     : https://prove2.me/theorems/e37f02dc-3916-49c6-a4b4-1c8c7fc1c648
-- title:
--   Cycle cover and its length (Section 7)
-- statement:
--   A **cycle cover** of a graph $G$ is a set $\mathcal F$ of cycles of $G$ such that every edge of $G$ belongs to at least one cycle of $\mathcal F$. The **length** of $\mathcal F$ is the sum of the lengths of its cycles,
--
--   $$\ell(\mathcal F) = \sum_{C \in \mathcal F} |C| .$$
--
--   The shortest length of a cycle cover is the quantity bounded by the Alon–Tarsi conjecture ($7m/5$ for bridgeless graphs with $m$ edges) and by the $4m/3$ bound of this mission.
--
--   **Formalization Note** Cycles are edge sets in the sense of `IsCycleEdges`, and $\mathcal F$ is a `Finset` of them, i.e. a set as in the paper. `coverLength F` is $\sum_{C \in F} |C|$, the length of a cycle being its number of edges.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 23, Section 7

import Mathlib
import Definitions.Def_SnarkGen_CycleCover_IsCycleEdges

namespace SnarkGen.CycleCover

/-- arXiv:1206.6690v3, p. 23: a *cycle cover* of `G` is a set `F` of cycles of `G` (each given
by its edge set) such that every edge of `G` belongs to at least one cycle of `F`. -/
def IsCycleCover {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (F : Finset (Finset (Sym2 V))) : Prop :=
  (∀ C ∈ F, IsCycleEdges G C) ∧ ∀ e ∈ G.edgeSet, ∃ C ∈ F, e ∈ C

/-- arXiv:1206.6690v3, p. 23: the *length* of a cycle cover is the sum of the lengths (numbers
of edges) of its cycles. -/
def coverLength {V : Type*} (F : Finset (Finset (Sym2 V))) : ℕ :=
  ∑ C ∈ F, C.card

end SnarkGen.CycleCover


