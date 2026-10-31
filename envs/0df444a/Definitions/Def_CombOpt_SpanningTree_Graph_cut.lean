-- Prove2me | Definitions.Def_CombOpt_SpanningTree_Graph_cut
-- name    : CombOpt_SpanningTree_Graph_cut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:58.693389+00:00
-- url     : https://prove2.me/theorems/28d5d2b1-295d-4b74-8edc-f448faaf7979
-- title:
--   Cut $\delta(A)$
-- statement:
--   For a set $A\subseteq V$ of nodes,
--   $$\delta(A)=\{e\in E : e \text{ has an end in } A \text{ and an end in } V\setminus A\}.$$
--   A set of the form $\delta(A)$ is a **cut** of $G$. A loop has both ends equal, so it lies in no cut.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph

namespace CombOpt.SpanningTree

open Classical in
/-- **The cut δ(A).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 12 (PDF p. 21): "For a graph G = (V, E) and A ⊆ V, we denote by δ(A) the set
{e ∈ E : e has an end in A and an end in V\A} … A set of the form δ(A) for some A is called a
cut of G."

`G.cut A` is the set of edges having an end in `A` and an end outside `A`.

**Formalization Note.** A loop has both ends equal, so it is in no cut, as the book's definition
gives. -/
noncomputable def Graph.cut {V E : Type*} [Fintype E] (G : Graph V E) (A : Finset V) :
    Finset E :=
  Finset.univ.filter (fun e => (∃ a ∈ G.ends e, a ∈ A) ∧ ∃ b ∈ G.ends e, b ∉ A)

end CombOpt.SpanningTree


