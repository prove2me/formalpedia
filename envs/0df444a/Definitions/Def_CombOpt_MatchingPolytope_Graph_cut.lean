-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_Graph_cut
-- name    : CombOpt_MatchingPolytope_Graph_cut
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:42.692301+00:00
-- url     : https://prove2.me/theorems/dadc5caa-a094-4cc6-81bd-84f8f0e24075
-- title:
--   The cut $\delta(A)$ of a node set
-- statement:
--   For a graph $G=(V,E)$ and $A\subseteq V$, the **cut** $\delta(A)$ is the set of edges having an end in $A$ and an end in $V\setminus A$:
--   $$\delta(A)=\{e\in E:\ e \text{ has an end in } A \text{ and an end in } V\setminus A\}.$$
--   For a node $v$ one writes $\delta(v)=\delta(\{v\})$. A loop has both ends equal and so lies in no cut.
--
--   The degree constraints $x(\delta(v))\le1$ of (6.7) and $x(\delta(v))=1$ of (6.3), and the odd-cut constraints of (6.3), are sums over cuts.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §2.1, p. 12 (PDF p. 21)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_Graph

namespace CombOpt.MatchingPolytope

open Classical in
/-- **The cut δ(A).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §2.1, p. 12 (PDF p. 21): "we denote by δ(A) the set {e ∈ E : e has an end in A and an
end in V\A}". For a node `v`, `δ(v)` abbreviates `δ({v})` (used in (6.3) and (6.7)).

`G.cut A` is the set of edges having an end in `A` and an end outside `A`.

**Formalization Note.** A loop has both ends equal, so it is in no cut, as the book's definition
gives. -/
noncomputable def Graph.cut {V E : Type*} [Fintype E] (G : Graph V E) (A : Finset V) :
    Finset E :=
  Finset.univ.filter (fun e => (∃ a ∈ G.ends e, a ∈ A) ∧ ∃ b ∈ G.ends e, b ∉ A)

end CombOpt.MatchingPolytope


