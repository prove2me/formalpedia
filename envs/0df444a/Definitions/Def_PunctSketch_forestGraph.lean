-- Prove2me | Definitions.Def_PunctSketch_forestGraph
-- name    : PunctSketch_forestGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:33.210197+00:00
-- url     : https://prove2.me/theorems/276d8bec-f7a1-4dba-aaba-08fb26182a91
-- title:
--   A spanning forest of $G\setminus F$
-- statement:
--   A finite set $T$ of unordered pairs is read as a graph. $T$ is a spanning forest of $G\setminus F$ when each of its pairs is an edge of $G$ with no endpoint in $F$, it has no cycle, and two vertices are connected in $T\setminus F$ exactly when they are connected in $G\setminus F$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.4, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_PunctSketch_ConnAvoid

namespace PunctSketch

/-- The graph whose edges are the non-diagonal pairs of `T`: the purported forest as a graph. Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…),
§5.1, p.16. -/
def forestGraph {V : Type*} (T : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (T : Set (Sym2 V))

/-- **A spanning forest of `G ∖ F`.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, p.21: "𝒯(F) is a spanning forest of G ⧵ F". Every
pair of `T` is an edge of `G` avoiding `F`, `T` has no cycle, and `T` connects exactly the vertices
that `G ∖ F` connects. -/
def IsSpanningForestOf {V : Type*} (G : SimpleGraph V) (F : Finset V) (T : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ T, e ∈ G.edgeSet ∧ ∀ x ∈ e, x ∉ F) ∧ (forestGraph T).IsAcyclic ∧
    ∀ x y, ConnAvoid (forestGraph T) F x y ↔ ConnAvoid G F x y

end PunctSketch


