-- Prove2me | Definitions.Def_opg500_eight_vertex_graph
-- name    : opg500_eight_vertex_graph
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-07T04:06:43.082794+00:00
-- url     : https://prove2.me/theorems/3364753c-d40b-447f-adee-420e64289ce1
-- title:
--   The fixed eight-vertex OPG-500 candidate graph
-- statement:
--   This definition fixes a simple graph $H$ on $\{0,1,\ldots,7\}$. Vertices $0,1,2,3$ form the core and vertices $4,5,6,7$ form the apex set. Its eighteen undirected edges are
--
--   $$
--   01,02,03,04,05,06,12,13,14,15,17,23,24,26,27,35,36,37.
--   $$
--
--   The bundle also records twelve vertex triples as data for the later peripheral-cycle classification. Their presence in the definition does not assert that they are peripheral or exhaustive; those facts are a separate theorem target.
-- source:
--   Frozen candidate graph and labels: https://github.com/vibemathing/problem-opg-500-geodesic-cycles/blob/a41fe59b4535851ea55f6e868e938b9aaf81e924/research/artifacts/candidates/opg500-a01-c10/tight-rank.md

import Definitions.Def_opg500_weighted_cycle_models

open Set
open scoped Sym2

namespace OPG500Counterexample

abbrev Vertex := Fin 8

def coreVertices : Finset Vertex := {0, 1, 2, 3}

def apexVertices : Finset Vertex := {4, 5, 6, 7}

/-- The frozen list of the eighteen undirected edges of the candidate graph. -/
def eightVertexEdges : Finset (Sym2 Vertex) :=
  {s(0, 1), s(0, 2), s(0, 3), s(0, 4), s(0, 5), s(0, 6),
   s(1, 2), s(1, 3), s(1, 4), s(1, 5), s(1, 7),
   s(2, 3), s(2, 4), s(2, 6), s(2, 7),
   s(3, 5), s(3, 6), s(3, 7)}

/-- The fixed eight-vertex graph proposed as a universal obstruction. -/
def H : SimpleGraph Vertex :=
  SimpleGraph.fromEdgeSet (eightVertexEdges : Set (Sym2 Vertex))

/-- The twelve vertex triples proposed to be exactly the peripheral cycles of `H`. -/
def peripheralTriples : Finset (Finset Vertex) :=
  [[0, 1, 4], [0, 1, 5], [0, 2, 4], [0, 2, 6],
   [0, 3, 5], [0, 3, 6], [1, 2, 4], [1, 2, 7],
   [1, 3, 5], [1, 3, 7], [2, 3, 6], [2, 3, 7]].map List.toFinset |>.toFinset

end OPG500Counterexample


