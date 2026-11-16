-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Graphs
-- name    : ConstrainedCorrelationRepulsion_Main_Supplement_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:03:07.418425+00:00
-- url     : https://prove2.me/theorems/12d0e092-a873-4bec-a5d1-bc167c6590e5
-- title:
--   Unsigned graphs and the cluster-deletion embedding
-- statement:
--   Let $G$ be a finite simple graph on $n$ labelled vertices. Its cluster-deletion embedding has positive graph $G$, no must-links, and all nonedges as cannot-links. A deletion set consists only of original edges and leaves a disjoint union of cliques. The only cluster-deletion optimum used here is
--
--   $$\operatorname{OPT}_{\rm del}(G)=\operatorname{OPT}(G,\varnothing,\overline G).$$
--
--   The symbols $m$, $\omega(G)$ and $\tau(G)$ denote the number of edges, maximum clique size and minimum vertex-cover size. The join $G\vee K_t$ has the original $n$ vertices first and $t$ new universal vertices. Empty graphs and singleton graphs are included; $\omega(\varnothing)=\tau(\varnothing)=0$. A partition's deletion set contains exactly its separated original edges.
--
--   These definitions connect the unsigned graph arguments to the existing signed objective. Cliques and vertex covers use Mathlib's general predicates; graph structure is not defined a second time. The minima and maximum are mathematical specifications, never operations offered to a program.
--
--   Differences from the source:
--   - encoding: arbitrary finite unsigned vertex sets → vertices labelled by $\mathrm{Fin}(n)$; reason: every finite simple graph admits this labelling, including the empty graph.
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), §7 and Definition 7.1, printed pp.35–36 (PDF pp.36–37)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Instance

namespace ConstrainedCorrelationRepulsion.Main.Supplement

open Classical

/-- §7: unsigned finite simple graphs use Mathlib's general graph object. -/
abbrev Graph (n : ℕ) := SimpleGraph (Fin n)

/-- The cluster-deletion subclass, with every nonedge forbidden. -/
def deletionInstance {n : ℕ} (G : Graph n) : Instance n :=
  ⟨G, ⊥, Gᶜ⟩

/-- A graph is a disjoint union of cliques, including isolated vertices and the empty graph. -/
def IsClusterGraph {n : ℕ} (G : Graph n) : Prop :=
  ∀ u v w, (u = v ∨ G.Adj u v) → (v = w ∨ G.Adj v w) → (u = w ∨ G.Adj u w)

/-- A deletion set contains only existing (unordered) edges, and leaves a cluster graph. -/
def IsDeletionSet {n : ℕ} (G : Graph n) (D : Finset (Sym2 (Fin n))) : Prop :=
  (↑D : Set (Sym2 (Fin n))) ⊆ G.edgeSet ∧ IsClusterGraph (G.deleteEdges D)

/-- There is just one objective: the published constrained OPT on the deletion embedding. -/
noncomputable def deletionOPT {n : ℕ} (G : Graph n) : ℕ := OPT (deletionInstance G)

noncomputable def edgeCount {n : ℕ} (G : Graph n) : ℕ := G.edgeFinset.card

/-- Mathematical specification only, never an algorithmic primitive. -/
noncomputable def omega {n : ℕ} (G : Graph n) : ℕ := G.cliqueNum

noncomputable def tau {n : ℕ} (G : Graph n) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (Fin n), G.IsVertexCover S ∧ S.card = k}

/-- Definition 7.1: old vertices first, followed by the universal clique. -/
noncomputable def joinClique {n : ℕ} (G : Graph n) (t : ℕ) : Graph (n+t) :=
  SimpleGraph.fromRel fun u v =>
    if h : u.val < n ∧ v.val < n then
      G.Adj ⟨u.val,h.1⟩ ⟨v.val,h.2⟩
    else True

/-- The original edges separated by a partition; its feasibility prevents joining nonedges. -/
noncomputable def partitionDeletions {n : ℕ} (G : Graph n) (P : Partition n) :
    Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter (fun e => P e.out.1 ≠ P e.out.2)

end ConstrainedCorrelationRepulsion.Main.Supplement


