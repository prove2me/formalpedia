-- Prove2me | Definitions.Def_EdgeDomSets_NPC_Supplement_TotalGraph
-- name    : EdgeDomSets_NPC_Supplement_TotalGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:02:04.140221+00:00
-- url     : https://prove2.me/theorems/e6168230-a7a9-4c83-9579-5a86d140ca88
-- title:
--   §3, p. 368 — the total graph
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph. Its total graph $T(G)$ has one vertex for each vertex of $G$ and one for each actual edge of $G$. Two vertex-type elements are adjacent precisely when adjacent in $G$; a vertex-type element and an edge-type element are adjacent precisely when incident; two distinct edge-type elements are adjacent precisely when they share an endpoint:
--
--   $$
--   V(T(G))=V\sqcup E.
--   $$
--
--   This common construction supplies the graph in LEMMAS 1–2 and THEOREMS 3–5. No edge-type element is adjacent to itself.
--
--   **Formalization Note** The carrier is the disjoint sum $V\oplus G.\mathrm{edgeSet}$. Symmetry and irreflexivity are structural proofs in the definition file. The general graph is Mathlib's `SimpleGraph`.
-- source:
--   Yannakakis, Gavril, Edge dominating sets in graphs, SIAM J. Appl. Math. 38(3) (1980) 364–372, p. 368, §3 (total graph); p. 364, §1 (adjacency)

import Mathlib

namespace EdgeDomSets.NPC.Supplement

/-- §3, p. 368: adjacency on the disjoint union of vertices and actual edges of G. -/
def totalAdj {V : Type} (G : SimpleGraph V) : (V ⊕ G.edgeSet) → (V ⊕ G.edgeSet) → Prop
  | .inl v, .inl w => G.Adj v w
  | .inl v, .inr e => v ∈ e.val
  | .inr e, .inl v => v ∈ e.val
  | .inr e, .inr f => e ≠ f ∧ ∃ v, v ∈ e.val ∧ v ∈ f.val

/-- Total graph: vertex adjacency, vertex–edge incidence, and adjacency of distinct edges. -/
def totalGraph {V : Type} (G : SimpleGraph V) : SimpleGraph (V ⊕ G.edgeSet) where
  Adj := totalAdj G
  symm := by
    constructor
    intro a b h
    cases a with
    | inl v =>
      cases b with
      | inl w => exact h.symm
      | inr e => exact h
    | inr e =>
      cases b with
      | inl v => exact h
      | inr f =>
        obtain ⟨hne, v, he, hf⟩ := h
        exact ⟨hne.symm, v, hf, he⟩
  loopless := by
    constructor
    intro a h
    cases a with
    | inl v => exact G.loopless.irrefl v h
    | inr e => exact h.1 rfl

end EdgeDomSets.NPC.Supplement


