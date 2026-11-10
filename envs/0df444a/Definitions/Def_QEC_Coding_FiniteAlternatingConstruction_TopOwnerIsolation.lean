-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
-- name    : QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T00:10:19.637217+00:00
-- url     : https://prove2.me/theorems/7e03f237-2db2-4194-9ea9-2232a7e42979
-- title:
--   Top Owner Isolation
-- statement:
--   Definitions and structural lemmas for Top Owner Isolation, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
set_option autoImplicit false
namespace QEC.Coding.BDL26TopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical
noncomputable abbrev graph := decodingGraph scaleFive 4
abbrev Node := graph.Node
def topNode (v : Vertex (state scaleFive 3).presentation) : Node :=
  ⟨(4 : Fin 5), v⟩
def TopMarksAreZ (M : Finset Node) : Prop :=
  ∀ v : Vertex (state scaleFive 3).presentation,
    topNode v ∈ M → ∃ z, v = Vertex.z z
def markedAdjacent (M : Finset Node) (u v : {w : Node // w ∈ M}) : Prop :=
  graph.adjacent u.val v.val
noncomputable def markedComponent (M : Finset Node) (a : {w : Node // w ∈ M}) :
    Finset {w : Node // w ∈ M} :=
  Finset.univ.filter (Relation.ReflTransGen (markedAdjacent M) a)
end QEC.Coding.BDL26TopOwnerIsolation


