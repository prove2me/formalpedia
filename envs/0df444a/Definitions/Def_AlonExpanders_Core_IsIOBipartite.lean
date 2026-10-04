-- Prove2me | Definitions.Def_AlonExpanders_Core_IsIOBipartite
-- name    : AlonExpanders_Core_IsIOBipartite
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:45:22.433987+00:00
-- url     : https://prove2.me/theorems/dd049699-e9f0-48ad-9aae-3ba3f099affc
-- title:
--   Bipartite graph on inputs $I$ and outputs $O$
-- statement:
--   Let $I$ and $O$ be two disjoint sets of vertices, the **inputs** and the **outputs**, and let $G$ be a finite simple graph on the vertex set $V = I \sqcup O$. The graph $G$ is **bipartite on $(I, O)$**, written $G = (I, O; E)$, if every edge of $G$ joins an input to an output:
--
--   $$
--   \forall\, i, i' \in I:\ ii' \notin E, \qquad \forall\, o, o' \in O:\ oo' \notin E.
--   $$
--
--   This is the setting of every expander in the paper: the expansion conditions quantify over sets of inputs, and bipartiteness guarantees that the neighbours of a set of inputs are outputs.
--
--   **Formalization Note** The vertex type is the sum type `I ⊕ O`; inputs are `Sum.inl i` and outputs `Sum.inr o`. The predicate is named `IsIOBipartite` to avoid confusion with Mathlib's `SimpleGraph.IsBipartite`, which asks only for the existence of some 2-colouring.
-- source:
--   Alon, Eigenvalues and expanders, Combinatorica 6 (1986), p. 83, Section 1 (bipartite graph on the sets of vertices I (inputs) and O (outputs))

import Mathlib

namespace AlonExpanders.Core

/-- `G` is a bipartite graph on the sets of vertices `I` (inputs) and `O` (outputs)
(Alon, *Eigenvalues and expanders*, Combinatorica 6 (1986), §1, p. 83): the vertex set is the
disjoint union `I ⊕ O` and no edge joins two inputs or two outputs. -/
def IsIOBipartite {I O : Type} (G : SimpleGraph (I ⊕ O)) : Prop :=
  (∀ i i' : I, ¬ G.Adj (Sum.inl i) (Sum.inl i')) ∧ (∀ o o' : O, ¬ G.Adj (Sum.inr o) (Sum.inr o'))

end AlonExpanders.Core


