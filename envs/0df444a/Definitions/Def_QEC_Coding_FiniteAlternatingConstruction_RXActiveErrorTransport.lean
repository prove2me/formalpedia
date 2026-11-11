-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXActiveErrorTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T13:01:00.090537+00:00
-- url     : https://prove2.me/theorems/dd855757-9bf3-4d4f-aa75-07b22aa375de
-- title:
--   RXActive Error Transport
-- statement:
--   Definitions and structural lemmas for RXActive Error Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXActiveErrorTransport.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Theorems.Thm_QEC_Coding_BDL26RXXStarTransport_mem_incidentQ
attribute [local simp] QEC.Coding.BDL26RXXStarTransport.mem_incidentQ


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXActiveErrorTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open BDL26BoundedValence BDL26GraphQuantitativeBounds
open scoped BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
def xPiece (E : Upper S depth i) (x : XCoord S i) : Finset (FamilyQ S depth i.succ) :=
  (rxLx S depth i h).correctionRegion x ∩ hammingSupport E
def qPiece (E : Upper S depth i) (q : QCoord S i) : Finset (FamilyQ S depth i.succ) :=
  (rxLq S depth i h).correctionRegion q ∩ hammingSupport E
def activeX (E : Upper S depth i) : Finset (XCoord S i) :=
  Finset.univ.filter fun x => (xPiece S depth i h E x).Nonempty
def activeQ (E : Upper S depth i) : Finset (QCoord S i) :=
  Finset.univ.filter fun q => (qPiece S depth i h E q).Nonempty
def incidentEquiv (x : XCoord S i) :
    {q : QCoord S i // q ∈ incidentQ S depth i x} ≃
      {q : QCoord S i // (state S i.val).presentation.xq x q=true} where
  toFun q := ⟨q.val,(mem_incidentQ S depth i x q.val).mp q.property⟩
  invFun q := ⟨q.val,(mem_incidentQ S depth i x q.val).mpr q.property⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl
def N (a b : Upper S depth i) : Finset (QCoord S i) :=
  BDL26RXFiniteBlockTransport.neighbors S depth i (activeX S depth i h (a+b)) (activeQ S depth i h (a+b))
def Phi (a b : Upper S depth i) : Potential S depth i :=
  BDL26RXFiniteBlockTransport.Phi S depth i h (activeX S depth i h (a+b)) a b
def R (a b : Upper S depth i) : Upper S depth i :=
  BDL26RXFiniteBlockTransport.R S depth i h (activeX S depth i h (a+b)) a b
def L (a b : Upper S depth i) : Lower S depth i :=
  BDL26RXFiniteBlockTransport.L S depth i h (activeX S depth i h (a+b)) a b
def NZ (a b : Upper S depth i) : Finset (ZCoord S i) :=
  BDL26RXFiniteBlockTransport.neighborZ S depth i (activeX S depth i h (a+b)) (activeQ S depth i h (a+b))
open BDL26FiniteAlternatingCore
end QEC.Coding.BDL26RXActiveErrorTransport


