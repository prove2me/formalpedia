-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXQEdgePairTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:15:52.680689+00:00
-- url     : https://prove2.me/theorems/efb6dfc0-ede9-4681-af85-7a8a34c0d869
-- title:
--   RXQEdge Pair Transport
-- statement:
--   Definitions and structural lemmas for RXQEdge Pair Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXQEdgePairTransport.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_HigherRXFaceTower
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RZLocalEdgeTower
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXQEdgePairTransport
open MultiscaleDecoder BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalizedHistoryErrorDescent BDL26CSSHamiltonian BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26OwnerIncidenceMasks BDL26HistoryLogicalResidual BDL26TannerLocalRegularity
open scoped Classical BigOperators
def qEdgeOwner (S : OddScale) (j : Nat) (q : Physical S (2*j+3))
    (e : QDoubleCylinderEdge (transposePresentation (state S (2*j+3)).presentation) q S) :
    (state S (2*j+4)).presentation.X :=
  BDL26RZPhysicalXStarTransport.upperXChart S (2*j+4) ⟨2*j+3,by omega⟩
    (by change ¬(2*j+3)%2=0; omega)
    (.inl (.inr ⟨q,e⟩))
abbrev Seed (S : OddScale) (j : Nat) :=
  Σ q : Physical S (2*j+3),
    Σ e : QDoubleCylinderEdge (transposePresentation (state S (2*j+3)).presentation) q S,
      DoubleCylinderEdge (state S (2*j+4)).presentation (qEdgeOwner S j q e) S
def seedPhysical (S : OddScale) (j : Nat) (a : Seed S j) : Physical S (2*j+5) :=
  BDL26RXDecoderAdapter.rxPhysicalQEquiv S (2*j+5) ⟨2*j+4,by omega⟩
    (by change (2*j+4)%2=0; omega)
    (.inl ⟨qEdgeOwner S j a.1 a.2.1,a.2.2⟩)
abbrev rxIndex := BDL26HigherRXFaceTower.rxIndex
abbrev rzIndex := BDL26HigherRXFaceTower.rzIndex
theorem index_pair (N j : Nat) (hN : 2*j+3≤N) :
    (rxIndex N j hN).castSucc=(rzIndex N j hN).succ :=
  (BDL26HigherRXFaceTower.seed_indices N j hN).2.2.symm
theorem rx_even (N j : Nat) (hN : 2*j+3≤N) : (Edge N (rxIndex N j hN)).val%2=0 := by
  exact BDL26HigherRXFaceTower.rx_index_even N j hN
theorem rz_odd (N j : Nat) (hN : 2*j+3≤N) : ¬(Edge N (rzIndex N j hN)).val%2=0 := by
  exact BDL26HigherRXFaceTower.rz_index_odd N j hN
def middle (S : OddScale) (N : Nat) (sigma tau : TopInput S N) (j : Nat) (hN : 2*j+3≤N)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ) :
    LocalizedWord S N sigma tau (rzIndex N j hN).succ :=
  cast (congrArg (LocalizedWord S N sigma tau) (index_pair N j hN))
    (step S N sigma tau (rxIndex N j hN) w).lower
def pairResult (S : OddScale) (N : Nat) (sigma tau : TopInput S N) (j : Nat) (hN : 2*j+3≤N)
    (w : LocalizedWord S N sigma tau (rxIndex N j hN).succ) :=
  step S N sigma tau (rzIndex N j hN) (middle S N sigma tau j hN w)
end QEC.Coding.BDL26RXQEdgePairTransport


