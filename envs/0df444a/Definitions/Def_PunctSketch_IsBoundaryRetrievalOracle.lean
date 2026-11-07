-- Prove2me | Definitions.Def_PunctSketch_IsBoundaryRetrievalOracle
-- name    : PunctSketch_IsBoundaryRetrievalOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:46.502192+00:00
-- url     : https://prove2.me/theorems/06252aed-1ead-4bf8-be17-1fd2f242c4b0
-- title:
--   A boundary retrieval oracle for $G\setminus F$ (Definition 2.2)
-- statement:
--   A procedure $\mathrm{BR}$ from vertex sets to sets of unordered pairs is a boundary retrieval oracle for $G\setminus F$ with capacity $s$ when, for each $C$ disjoint from $F$ with $|\partial_{-F}C|\le s$, one has $\mathrm{BR}(C)=\partial_{-F}C$. When the boundary is larger, $\mathrm{BR}(C)$ can be arbitrary.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Definition 2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_PunctSketch_puncturedBoundary

namespace PunctSketch

/-- **A boundary retrieval oracle for `G ∖ F` (Definition 2.2).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Definition 2.2, p.6: "If
|∂C| ≤ s, then BR(C) = ∂C; if, instead, |∂C| > s, then BR(C) can be arbitrary."

Queries are the sets `C` disjoint from `F`; the boundary is taken in `G ∖ F`, which is
`puncturedBoundary G F C`. -/
def IsBoundaryRetrievalOracle {V : Type*} (G : SimpleGraph V) (F : Finset V) (cap : ℕ)
    (BR : Finset V → Finset (Sym2 V)) : Prop :=
  ∀ C : Finset V, Disjoint C F → (puncturedBoundary G F C).ncard ≤ cap →
    (BR C : Set (Sym2 V)) = puncturedBoundary G F C

end PunctSketch


