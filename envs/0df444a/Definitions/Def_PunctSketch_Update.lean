-- Prove2me | Definitions.Def_PunctSketch_Update
-- name    : PunctSketch_Update
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:43.99431+00:00
-- url     : https://prove2.me/theorems/a787809d-b66f-47c2-b14c-81233109d70b
-- title:
--   Edge updates and the graph of a stream
-- statement:
--   An update of a turnstile stream is an edge $\{u,v\}$ and one bit: insert or delete. Applying the updates of a list in order, from the empty graph, gives the final graph of the stream.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §1, p.1 (PDF p.2)

import Mathlib

namespace PunctSketch

/-- **An edge update of a turnstile stream.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §1, p.1: "a sequence of edge insertions and
deletions to an underlying n-vertex graph (which starts out empty)". `insert = true` inserts the
edge `{u, v}`, `insert = false` deletes it. -/
structure Update (n : ℕ) where
  u : Fin n
  v : Fin n
  insert : Bool

open Classical in
/-- The graph after applying one update. -/
noncomputable def Update.apply {n : ℕ} (e : Update n) (G : SimpleGraph (Fin n)) :
    SimpleGraph (Fin n) :=
  if e.insert then G ⊔ SimpleGraph.edge e.u e.v else G \ SimpleGraph.edge e.u e.v

/-- The graph at the end of a stream that starts from the empty graph. -/
noncomputable def streamGraph {n : ℕ} (σ : List (Update n)) : SimpleGraph (Fin n) :=
  σ.foldl (fun G e => e.apply G) ⊥

end PunctSketch


