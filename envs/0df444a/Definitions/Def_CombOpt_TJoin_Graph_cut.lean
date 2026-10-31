-- Prove2me | Definitions.Def_CombOpt_TJoin_Graph_cut
-- name    : CombOpt_TJoin_Graph_cut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:26.680834+00:00
-- url     : https://prove2.me/theorems/ede14a48-8b8c-4631-bb06-130ba452951c
-- title:
--   The cut $\delta(A)$
-- statement:
--   For a graph $G=(V,E)$ and a set of nodes $A\subseteq V$, the **cut**
--
--   $$\delta(A)=\{e\in E:\ e \text{ has an end in } A \text{ and an end in } V\setminus A\}.$$
--
--   For a node $v$, $\delta(v)=\delta(\{v\})$ is the set of non-loop edges incident with $v$. A loop lies in no cut.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_TJoin_Graph

namespace CombOpt.TJoin

/-- **The cut δ(A).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 12 (PDF p. 21): "we denote by δ(A) the set {e ∈ E : e has an end in A and an end
in V\A}". The star of a node is `δ(v) = δ({v})`.

`G.cut A` is the set of edges having an end in `A` and an end in the complement of `A`.

**Formalization Note.** A loop has both ends equal, so it lies in no cut, and in particular in no
`δ(v)`, exactly as the book's definition gives. -/
def Graph.cut {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (G : Graph V E)
    (A : Finset V) : Finset E :=
  Finset.univ.filter (fun e => (∃ a ∈ A, a ∈ G.ends e) ∧ ∃ b ∈ Aᶜ, b ∈ G.ends e)

end CombOpt.TJoin


