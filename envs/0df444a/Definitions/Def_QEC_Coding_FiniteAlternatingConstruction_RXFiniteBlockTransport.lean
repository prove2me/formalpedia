-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:54:50.1309+00:00
-- url     : https://prove2.me/theorems/69bfb56e-a0d7-49d4-b94a-74bb1a9514c9
-- title:
--   RXFinite Block Transport
-- statement:
--   Definitions and structural lemmas for RXFinite Block Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXFiniteBlockTransport.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXXStarTransport
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXFiniteBlockTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
def xBlocks (X0 : Finset (XCoord S i)) : Finset (FamilyQ S depth i.succ) :=
  X0.biUnion ((rxLx S depth i h).correctionRegion)
def qBlocks (Q0 : Finset (QCoord S i)) : Finset (FamilyQ S depth i.succ) :=
  Q0.biUnion ((rxLq S depth i h).correctionRegion)
def neighbors (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i)) : Finset (QCoord S i) :=
  Q0 ∪ X0.biUnion (incidentQ S depth i)
def star (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i)) :
    Finset (FamilyQ S depth i.succ) :=
  xBlocks S depth i h X0 ∪ qBlocks S depth i h (neighbors S depth i X0 Q0)
def degreeZeroBlocks (X0 : Finset (XCoord S i)) : Finset (FamilyX S depth i.succ) :=
  X0.biUnion (degreeZeroBlock S depth i h)
def neighborZ (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i)) : Finset (ZCoord S i) :=
  Finset.univ.filter fun z => ∃ q ∈ neighbors S depth i X0 Q0,
    (state S i.val).presentation.qz q z=true
def Localized (X0 : Finset (XCoord S i)) (Q0 : Finset (QCoord S i))
    (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ xBlocks S depth i h X0 ∪ qBlocks S depth i h Q0
def Phi (X0 : Finset (XCoord S i)) (a b : Upper S depth i) : Potential S depth i :=
  ∑ x ∈ X0, BDL26RXXStarTransport.potential S depth i h x a b
def R (X0 : Finset (XCoord S i)) (a b : Upper S depth i) : Upper S depth i :=
  updated S depth i h a b + (indexedFamily S depth).coboundary0 i.succ (Phi S depth i h X0 a b)
def L (X0 : Finset (XCoord S i)) (a b : Upper S depth i) : Lower S depth i :=
  fun q => R S depth i h X0 a b (rxQVertexEquiv S depth i h q (0,Sum.inl (Sum.inl ()))).val
open BDL26FiniteAlternatingCore
def seedWord : Word BDL26Field BaseQubit := canonicalBasisWord (0 : BaseQubit)+canonicalBasisWord (4 : BaseQubit)
end QEC.Coding.BDL26RXFiniteBlockTransport


