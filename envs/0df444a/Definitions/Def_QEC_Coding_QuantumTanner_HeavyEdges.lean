-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
-- name    : QEC_Coding_QuantumTanner_HeavyEdges
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T00:28:49.594438+00:00
-- url     : https://prove2.me/theorems/060778a4-92ad-4fd0-82f4-8ef70b5096b7
-- title:
--   Heavy Edges
-- statement:
--   Definitions and structural lemmas for Heavy Edges, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
def unionCayleyGraph (X : LeftRightCayleySquareComplex G A B Square) : WeightedGraph G :=
  fun g h => (Finset.univ.filter fun a => X.leftGenerator a * g = h).card +
    (Finset.univ.filter fun b => g * X.rightGenerator b = h).card
def heavyUnionGraph (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) : WeightedGraph G := fun g h =>
  (Finset.univ.filter fun a => X.leftGenerator a * g = h ∧
    cutoff ≤ HammingWeight (rowRestriction a (X.localRestriction (g, side) x))).card +
  (Finset.univ.filter fun b => g * X.rightGenerator b = h ∧
    cutoff ≤ HammingWeight (columnRestriction b (X.localRestriction (g, side) x))).card
def oppositeHeavySet (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G) : Finset G :=
  Finset.univ.filter fun h => ∃ g ∈ normal, X.heavyUnionGraph side x cutoff g h ≠ 0
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex


