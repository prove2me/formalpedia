-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_NeighborViews
-- name    : QEC_Coding_QuantumTanner_NeighborViews
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:31:55.832941+00:00
-- url     : https://prove2.me/theorems/65e07a93-dc13-433f-8614-283129808037
-- title:
--   Neighbor Views
-- statement:
--   Definitions and structural lemmas for Neighbor Views, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NeighborViews.lean

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_QuantumTanner_LocalReduction
import Definitions.Def_QEC_Coding_QuantumTanner_HeavySelection
import Definitions.Def_QEC_Coding_QuantumTanner_ExceptionalVertices
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
def exceptionalLeftLabels (X : LeftRightCayleySquareComplex G A B Square)
    (g : G) (exceptional : Finset G) : Finset A :=
  Finset.univ.filter fun a => X.leftGenerator a * g ∈ exceptional
def exceptionalRightLabels (X : LeftRightCayleySquareComplex G A B Square)
    (g : G) (exceptional : Finset G) : Finset B :=
  Finset.univ.filter fun b => g * X.rightGenerator b ∈ exceptional
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex


