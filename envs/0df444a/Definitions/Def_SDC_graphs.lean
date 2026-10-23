-- Prove2me | Definitions.Def_SDC_graphs
-- name    : SDC_graphs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-23T04:12:54.554741+00:00
-- url     : https://prove2.me/theorems/db186fd3-1dbc-40f6-897f-81090704c107
-- title:
--   The Sidorenko counterexample pattern: the incidence graph of the 22 triples
-- statement:
--   The pattern of the counterexample: the incidence graph H of the 22 triples of Table 1 of the manuscript on 13 points. The 22 triples are given as a table of 3-element sets of the 13 points; the vertices of the pattern are the 13 points and the 22 triples; a point and a triple are adjacent when the point lies in the triple. The pattern has 13 + 22 vertices and 66 edges (three incidences per triple), and 66 is the exponent appearing in Sidorenko inequality for this pattern.
-- source:
--   Uploaded manuscript A finite counterexample to Sidorenko conjecture (SidorenkoCounterexample.lean.txt), namespace OAI.SidorenkoCounterexample: the definitions are taken verbatim from the manuscript and re-namespaced to SDC.

import Mathlib

/-!
# The Sidorenko counterexample pattern

The pattern layer of the SDC mission: the finite incidence pattern of the
uploaded manuscript A finite counterexample to Sidorenko conjecture (the
uploaded file SidorenkoCounterexample.lean.txt, namespace
OAI.SidorenkoCounterexample). The pattern is the incidence graph of the
22 triples of Table 1 of the manuscript on 13 points: a point and a triple
are adjacent when the point lies in the triple. The pattern has 13 + 22
vertices and 66 edges (three incidences per triple); 66 is the exponent
appearing in Sidorenko inequality for this pattern.

The definitions are taken verbatim from the manuscript, re-namespaced to
SDC. The homomorphism counting and density framework built on the pattern
is in Definitions.Def_SDC_density.
-/

namespace SDC

/-- The 22 triples of Table 1 of the manuscript, as Finsets of the 13
points. -/
def faces : Fin 22 → Finset (Fin 13) :=
  ![{0, 1, 3}, {0, 1, 9}, {0, 2, 3}, {0, 2, 9}, {1, 3, 10}, {1, 7, 10},
    {1, 7, 12}, {1, 9, 12}, {2, 3, 4}, {2, 4, 9}, {3, 4, 11}, {3, 10, 11},
    {4, 8, 9}, {4, 8, 11}, {5, 6, 7}, {5, 6, 11}, {5, 7, 10}, {5, 10, 11},
    {6, 7, 12}, {6, 8, 11}, {6, 8, 12}, {8, 9, 12}]

/-- The vertices of the pattern: the 13 points and the 22 triples. -/
abbrev PatternVertex := Fin 13 ⊕ Fin 22

/-- Incidence of the pattern: a point and a triple are adjacent when the
point lies in the triple. -/
def incidence : PatternVertex → PatternVertex → Prop
  | .inl point, .inr face => point ∈ faces face
  | .inr face, .inl point => point ∈ faces face
  | _, _ => False

/-- The pattern graph H: the incidence graph of the 22 triples. -/
def H : SimpleGraph PatternVertex where
  Adj := incidence
  symm.symm := by intro left right; cases left <;> cases right <;> simp [incidence]
  loopless.irrefl := by intro vertex; cases vertex <;> simp [incidence]

end SDC


