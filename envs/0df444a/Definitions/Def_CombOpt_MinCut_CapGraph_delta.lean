-- Prove2me | Definitions.Def_CombOpt_MinCut_CapGraph_delta
-- name    : CombOpt_MinCut_CapGraph_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:04.246641+00:00
-- url     : https://prove2.me/theorems/c7a33b52-c371-4acc-b45a-107059c45cde
-- title:
--   The cut $\delta(S)$ of a node set
-- statement:
--   For a graph $G=(V,E)$ and $S\subseteq V$, the **cut** $\delta(S)$ is the set of edges having an end in $S$ and an end in $V\setminus S$:
--
--   $$\delta(S)=\{e\in E : e \text{ has an end in } S \text{ and an end in } V\setminus S\}.$$
--
--   A set of the form $\delta(S)$ for some $S$ is a cut of $G$. For a node $v$, $\delta(v)=\delta(\{v\})$ is the star of $v$. A loop has both ends equal and so lies in no cut.
--
--   Cuts are the feasible solutions of the minimum cut problem and the objects compared in Proposition 3.35.
--
--   **Formalization Note** `S` is a `Finset V`; every subset is allowed, including $\emptyset$ and $V$ (whose cuts are empty), as in the book's definition of a cut.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph

namespace CombOpt.MinCut

open Classical in
/-- **The cut `δ(S)`.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 12
(PDF p. 21): "For a graph G = (V, E) and A ⊆ V, we denote by δ(A) the set {e ∈ E : e has an end in
A and an end in V\A} … A set of the form δ(A) for some A is called a cut of G."

`G.delta S` is the set of edges having an end in `S` and an end outside `S`. For a node `v`,
`G.delta {v}` is the star `δ(v)`.

**Formalization Note.** A loop has both ends equal, so it is in no cut, as the book's definition
gives; in particular `δ(v)` contains no loop. Any `S ⊆ V` is allowed (`δ(∅) = δ(V) = ∅`), as in
the book's definition of a cut. -/
noncomputable def CapGraph.delta {V E : Type*} [Fintype E] (G : CapGraph V E) (S : Finset V) :
    Finset E :=
  Finset.univ.filter (fun e => (∃ a ∈ G.ends e, a ∈ S) ∧ ∃ b ∈ G.ends e, b ∉ S)

end CombOpt.MinCut


