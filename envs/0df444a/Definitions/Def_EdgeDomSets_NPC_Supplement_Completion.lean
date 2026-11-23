-- Prove2me | Definitions.Def_EdgeDomSets_NPC_Supplement_Completion
-- name    : EdgeDomSets_NPC_Supplement_Completion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:06:41.648804+00:00
-- url     : https://prove2.me/theorems/616e815e-413f-4cb5-a43b-fc9d9160990b
-- title:
--   §3, pp. 368–369 — covered vertices and the associated total-graph set
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, let $M\subseteq E$, and let $V_M$ consist of all endpoints of members of $M$. The associated vertex set of the total graph and the edge part of a total-graph vertex set $A$ are
--
--   $$
--   S_G(M)=\{\operatorname{inr}(e):e\in M\}\cup\{\operatorname{inl}(v):v\in V\setminus V_M\},\qquad
--   E_G(A)=\{e\in E:\operatorname{inr}(e)\in A\}.
--   $$
--
--   These constructions give a single meaning to the source's expression $M\cup(V-V_M)$ throughout LEMMAS 1–2 and THEOREMS 3–4, and compute the set called $M$ in THEOREM 3 from $A$ itself.
--
--   **Formalization Note** Both constructions are finite sets on the disjoint-sum carrier of the imported total graph. For an arbitrary input pair set $M$, `completion` selects only actual edges of $G$ on the edge side; every theorem application assumes $M$ is a matching or an independent edge dominating set, so it contains no non-edges. Uncovered vertices are computed from the supplied $M$.
-- source:
--   Yannakakis, Gavril, Edge dominating sets in graphs, SIAM J. Appl. Math. 38(3) (1980) 364–372, pp. 368–369, §3, LEMMA 1 and THEOREM 3 notation; p. 364, §1 (V_M)

import Mathlib
import Definitions.Def_EdgeDomSets_NPC_Supplement_TotalGraph
import Definitions.Def_LoadBalMatch_Main_Matching

namespace EdgeDomSets.NPC.Supplement

/-- §3, p. 368: M ∪ (V − V_M), as vertices of the total graph.
On a non-edge set M this selects only actual edges; every application assumes M is a matching. -/
noncomputable def completion {V : Type} [Fintype V] (G : SimpleGraph V)
    (M : Finset (Sym2 V)) : Finset (V ⊕ G.edgeSet) := by
  classical
  exact Finset.univ.filter fun a => match a with
    | .inl v => ¬ LoadBalMatch.Main.Covers M v
    | .inr e => e.val ∈ M

/-- §3, pp. 368–369: the e-vertices of A, viewed as edges of G. -/
noncomputable def edgePart {V : Type} (G : SimpleGraph V)
    (A : Finset (V ⊕ G.edgeSet)) : Finset (Sym2 V) := by
  classical
  exact (A.toList.filterMap fun a => match a with
    | .inl _ => none
    | .inr e => some e.val).toFinset

end EdgeDomSets.NPC.Supplement


