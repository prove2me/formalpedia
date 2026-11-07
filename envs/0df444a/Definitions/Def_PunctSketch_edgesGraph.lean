-- Prove2me | Definitions.Def_PunctSketch_edgesGraph
-- name    : PunctSketch_edgesGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:43:18.668818+00:00
-- url     : https://prove2.me/theorems/c12867dd-9eda-4d02-852e-a37154a97c29
-- title:
--   The graph of a list of edges
-- statement:
--   The graph whose edges are the listed pairs. It is the current graph of a sequence of added edges in the [SSZ09] bound.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.4, p.21 (PDF p.22)

import Mathlib

namespace PunctSketch

/-- The graph with the listed edges. Used for [SSZ09]'s sequences of added edges (Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, p.21). -/
def edgesGraph {n : ℕ} (es : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ p ∈ es, e = s(p.1, p.2)}

end PunctSketch


