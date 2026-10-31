-- Prove2me | Definitions.Def_CombOpt_MinCostFlow_Digraph_delta
-- name    : CombOpt_MinCostFlow_Digraph_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:09.686957+00:00
-- url     : https://prove2.me/theorems/efa10c3c-2d83-4062-a409-2ff7b9a76150
-- title:
--   The cut $\delta(A)$ of arcs leaving $A$
-- statement:
--   For a digraph $G=(V,E)$ and $A\subseteq V$, the **cut** $\delta(A)$ is the set of arcs with tail in $A$ and head in $\bar A=V\setminus A$. The arcs entering $A$ form $\delta(\bar A)$.
--
--   For a vector $w$ on the arcs, $w(\delta(A))$ denotes $\sum(w_e : e\in\delta(A))$; this is how cut conditions such as the one in Theorem 3.18 are written.
--
--   **Formalization Note** Node subsets are `Finset V`, and $\bar A$ is the complement `Aᶜ`.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §3.2, p. 40 (PDF p. 49)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph

namespace CombOpt.MinCostFlow

/-- **The cut δ(A): arcs leaving A.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §3.2, p. 40 (PDF p. 49): "We call a set δ(R) = {vw : vw ∈ E, v ∈ R, w ∉ R}
for some R ⊆ V, a cut. … For any A ⊆ V we use Ā to denote V\A." The set δ(Ā) of arcs entering A is
`G.delta Aᶜ`.

**Formalization Note.** Node subsets are `Finset V`; a loop is in no cut. -/
def Digraph.delta {V E : Type*} [Fintype E] [DecidableEq V] (G : Digraph V E) (A : Finset V) :
    Finset E :=
  Finset.univ.filter (fun e => G.tail e ∈ A ∧ G.head e ∉ A)

end CombOpt.MinCostFlow


