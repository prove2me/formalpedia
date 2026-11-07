-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_CayleySquareGraph
-- name    : QEC_Coding_QuantumTanner_CayleySquareGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:32:14.968945+00:00
-- url     : https://prove2.me/theorems/868c54e3-a303-480c-a22c-a46e563c04bc
-- title:
--   Cayley Square Graph
-- statement:
--   Definitions and structural lemmas for Cayley Square Graph, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/CayleySquareGraph.lean

import Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionOperators
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
def leftCayleyGraph (X : LeftRightCayleySquareComplex G A B Square) : WeightedGraph G :=
  fun g h => (Finset.univ.filter fun a => X.leftGenerator a * g = h).card
def rightCayleyGraph (X : LeftRightCayleySquareComplex G A B Square) : WeightedGraph G :=
  fun g h => (Finset.univ.filter fun b => g * X.rightGenerator b = h).card
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex


