-- Prove2me | Definitions.Def_PunctSketch_ConnAvoid
-- name    : PunctSketch_ConnAvoid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:31.190196+00:00
-- url     : https://prove2.me/theorems/f06bdbdd-5f1b-4aa4-8a49-86dfc43fa82d
-- title:
--   Connected in $G\setminus F$
-- statement:
--   For a graph $G$ and a vertex set $F$, two vertices $x,y$ are related when neither lies in $F$ and they lie in one connected component of the induced subgraph $G\setminus F = G[V\setminus F]$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.4 (PDF p.5)

import Mathlib

namespace PunctSketch

/-- **Connected in `G ∖ F`.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.4: "G ⧵ Z for the subgraph obtained by deleting Z; note
that G ⧵ Z = G[V ⧵ Z]".

`ConnAvoid G F x y` says that `x` and `y` are vertices of `G ∖ F` in one connected component of
`G ∖ F`. It is false when `x` or `y` lies in `F`. -/
def ConnAvoid {V : Type*} (G : SimpleGraph V) (F : Finset V) (x y : V) : Prop :=
  ∃ (hx : x ∈ (F : Set V)ᶜ) (hy : y ∈ (F : Set V)ᶜ),
    (G.induce (F : Set V)ᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩

end PunctSketch


