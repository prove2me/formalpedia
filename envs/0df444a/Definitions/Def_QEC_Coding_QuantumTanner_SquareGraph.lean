-- Prove2me | Definitions.Def_QEC_Coding_QuantumTanner_SquareGraph
-- name    : QEC_Coding_QuantumTanner_SquareGraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:56:23.409203+00:00
-- url     : https://prove2.me/theorems/b670d8e7-cc28-41e6-8692-1a6280db1277
-- title:
--   Square Graph
-- statement:
--   Definitions and structural lemmas for Square Graph, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SquareGraph.lean

import Definitions.Def_QEC_Coding_QuantumTanner_Distance
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical
open QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]
def squareGraph (X : LeftRightCayleySquareComplex G A B Square) (side : Bool) :
    WeightedGraph G := fun g h =>
  (Finset.univ.filter fun q => X.Incident (g, side) q ∧ X.Incident (h, side) q ∧ g ≠ h).card
def supportSquareGraph (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) : WeightedGraph G := fun g h =>
  (Finset.univ.filter fun q => x q ≠ 0 ∧ X.Incident (g, side) q ∧
    X.Incident (h, side) q ∧ g ≠ h).card
def exceptionalVerticesOnSide (X : LeftRightCayleySquareComplex G A B Square)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) : Finset G :=
  (X.activeVerticesOnSide side x).filter fun g => cutoff ≤
    HammingWeight (X.localRestriction (g, side) x)
end QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex


