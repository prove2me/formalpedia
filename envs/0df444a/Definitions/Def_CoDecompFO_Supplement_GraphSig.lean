-- Prove2me | Definitions.Def_CoDecompFO_Supplement_GraphSig
-- name    : CoDecompFO_Supplement_GraphSig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:48:27.853198+00:00
-- url     : https://prove2.me/theorems/d0528dee-5700-4e7d-88a9-ec42320259c1
-- title:
--   Graphs as $\sigma_G$-structures; path co-decompositions and path co-width $\le w$
-- statement:
--   The **signature of graphs** $\sigma_G$ has one binary symbol $E$; a $\sigma_G$-structure is a directed graph with loops allowed and no parallel edges (¶2.1). A simple graph is the symmetric loopless $\sigma_G$-structure with $E=\{(x,y): x\sim y\}$.
--
--   A tree co-decomposition is a **path co-decomposition** if its auxiliary tree is a path, i.e. every node has at most two neighbours (¶1.6). A graph $G$ has **path co-width at most $w$** if some path co-decomposition of graphs of width at most $w$ has limit isomorphic to $G$ as a $\sigma_G$-structure:
--
--   $$\exists\,\mathcal T\ \text{path co-decomposition},\quad \mathrm{width}(\mathcal T)\le w,\quad \lim\mathcal T\cong G .$$
--
--   These are the objects of Theorem 1.11 and of the $(s,t)$-PATH problem of Theorem 1.14.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶1.6, p.2; ¶2.1 and ¶2.3, p.6; Theorem 1.11, p.3 (PDF pp.4, 5, 8)

import Mathlib
import Definitions.Def_CoDecompFO_Lim

set_option autoImplicit false

namespace CoDecompFO

namespace Supplement

open FirstOrder

/-- The **signature of graphs** `σ_G` (Bumpus et al., arXiv:2611.04658, held file sha256 d550d7af…, ¶2.1, p.6;
¶2.3, p.6): one binary relation symbol, the edge relation. "Throughout, all graphs are directed and allowed to
contain loops, but not parallel edges", so a graph is exactly a `σ_G`-structure. -/
abbrev graphSig : Sig := ⟨1, fun _ => 2⟩

/-- The edge relation `(x, y) ∈ E(G)` of a `σ_G`-structure. -/
def IsEdge {M : Type} [graphSig.lang.Structure M] (x y : M) : Prop :=
  graphSig.holds (0 : Fin 1) (show Fin (graphSig.ar 0) → M from ![x, y])

/-- A Mathlib simple graph as a `σ_G`-structure: "We think of undirected graphs G as symmetric, meaning that for
each arc (x, y) ∈ E(G) the arc (y, x) is also in G" (¶2.1, p.6). A simple graph has no loops. -/
@[reducible] def simpleGraphStructure {V : Type} (G : SimpleGraph V) : graphSig.lang.Structure V :=
  graphSig.structureOf (fun _ a => G.Adj (a 0) (a 1))

variable {σ : Sig}

/-- `T` is a **path co-decomposition** (¶1.6, p.2): "When the tree T is a path, we call T a path
co-decomposition". A tree is a path exactly when every node has at most two neighbours. -/
def IsPathCoDecomp (T : CoDecomp σ) : Prop := ∀ t, (T.graph.neighborSet t).ncard ≤ 2

/-- The simple graph `G` has **path co-width at most `w`** (¶1.6, p.2; Theorem 1.11, p.3): there is a path
co-decomposition of graphs of width at most `w` whose limit is isomorphic to `G` ("We say that G is the limit of T
if G is isomorphic to the graph obtained by recursively taking the pullbacks along the edges of T, i.e.,
G ≃ lim T"). The isomorphism is one of `σ_G`-structures: it preserves and reflects edges. -/
def PathCoWidthLE {V : Type} (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ T : CoDecomp graphSig, IsPathCoDecomp T ∧ width T ≤ w ∧
    Nonempty (@FirstOrder.Language.Equiv graphSig.lang T.Lim V _ (simpleGraphStructure G))

end Supplement

end CoDecompFO


