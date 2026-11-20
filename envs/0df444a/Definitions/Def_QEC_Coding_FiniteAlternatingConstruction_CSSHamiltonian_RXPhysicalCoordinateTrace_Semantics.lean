-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace_Semantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T08:11:45.402019+00:00
-- url     : https://prove2.me/theorems/8540f2ce-6a59-4553-b317-a87f462acce2
-- title:
--   Semantics
-- statement:
--   Definitions and structural lemmas for Semantics, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXPhysicalCoordinateTrace/Semantics.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXPhysicalCoordinateTrace
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LocalSearchFailureReduction
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXPhysicalCoordinateTrace
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26LocalizedHistoryErrorDescent BDL26RZMap1CoordinateBridge
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26OwnerIncidenceMasks
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder
open scoped Classical BigOperators
def LeafMeaning (S : OddScale) (N : Nat) (sigma tau : TopInput S N)
    (top : LocalizedWord S N sigma tau (TopIndex N)) : Leaf S → Prop
  | .c2 r => hammingSupport (path S N sigma tau top 0).word ⊆ {r}
  | .face a => hammingSupport (path S N sigma tau top 0).word ⊆
      BDL26RXPhysicalStarTransport.physicalXStar (state S 2).presentation
        (BDL26RXFaceEdgeTower.faceOwner S a.1 a.2.1)
  | .killed b => ∃ hb : b≤N,
      (path S N sigma tau top ⟨b,Nat.lt_succ_of_le hb⟩).word=0
  | @Leaf.primitive _ b p => ∃ hb : b≤N,
      hammingSupport (path S N sigma tau top ⟨b,Nat.lt_succ_of_le hb⟩).word ⊆ {p.physical}
end QEC.Coding.BDL26RXPhysicalCoordinateTrace


