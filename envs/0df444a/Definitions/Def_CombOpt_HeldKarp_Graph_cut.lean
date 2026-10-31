-- Prove2me | Definitions.Def_CombOpt_HeldKarp_Graph_cut
-- name    : CombOpt_HeldKarp_Graph_cut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:39.686984+00:00
-- url     : https://prove2.me/theorems/3acafe21-6486-4880-a37d-06fe30075d41
-- title:
--   The cut $\delta(A)$
-- statement:
--   For $A\subseteq V$, the **cut** $\delta(A)$ is the set of edges with one end in $A$ and the other end in $V\setminus A$. For a node $v$, $\delta(v)=\delta(\{v\})$ is the set of non-loop edges incident with $v$.
--
--   A loop is in no cut. For $x\in\mathbb R^E$ and $B\subseteq E$ we write $x(B)=\sum_{e\in B}x_e$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph

namespace CombOpt.HeldKarp

open Classical in
/-- **The cut δ(A).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 12
(PDF p. 21): "For a graph G = (V, E) and A ⊆ V, we denote by δ(A) the set {e ∈ E : e has an end in
A and an end in V\A}". For a node v, δ(v) means δ({v}).

`G.cut A` is the set of edges having an end in `A` and an end outside `A`.

**Formalization Note.** A loop has both ends equal, so it is in no cut, as the book's definition
gives. -/
noncomputable def Graph.cut {V E : Type*} [Fintype E] (G : Graph V E) (A : Finset V) :
    Finset E :=
  Finset.univ.filter (fun e => (∃ a ∈ G.ends e, a ∈ A) ∧ ∃ b ∈ G.ends e, b ∉ A)

end CombOpt.HeldKarp


