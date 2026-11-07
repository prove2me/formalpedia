-- Prove2me | Definitions.Def_PunctSketch_puncturedBoundary
-- name    : PunctSketch_puncturedBoundary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:48.652856+00:00
-- url     : https://prove2.me/theorems/c7c4a33f-7a24-4bbb-a0a7-f3b258b81499
-- title:
--   The punctured boundary (1)
-- statement:
--   The crossing pairs of $C$ with respect to $F$ are the unordered pairs with one endpoint in $C$, the other outside $C$, and no endpoint in $F$. The punctured boundary
--   $$\partial_{-F}C=\{e\in E: |e\cap C|=1,\ e\cap F=\emptyset\}$$
--   is the set of edges among them, that is the boundary of $C$ in $G\setminus F$.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.4 (PDF p.5), eq. (1)

import Mathlib

namespace PunctSketch

/-- The unordered pairs with one endpoint in `C`, the other outside `C`, and no endpoint in `F`:
"`{v, u}`, `v ∈ C`, `u ∉ C ∪ F`" (Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), p.12), for `C` disjoint from `F`. -/
def crossingPairs {V : Type*} (F C : Finset V) : Set (Sym2 V) :=
  {e | ∃ v u, e = s(v, u) ∧ v ∈ C ∧ v ∉ F ∧ u ∉ C ∧ u ∉ F}

/-- **The punctured boundary (1).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.4, eq. (1):
`∂_{−F} Z = {e ∈ E : |e ∩ Z| = 1, e ∩ F = ∅}`, the boundary of `Z` in `G ∖ F`. -/
def puncturedBoundary {V : Type*} (G : SimpleGraph V) (F C : Finset V) : Set (Sym2 V) :=
  G.edgeSet ∩ crossingPairs F C

end PunctSketch


