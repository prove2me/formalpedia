-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
-- name    : QEC_Coding_FiniteAlternatingConstruction_RXPhysicalStarTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T12:59:37.042372+00:00
-- url     : https://prove2.me/theorems/95ed98af-59e3-4386-870f-4555fe05c388
-- title:
--   RXPhysical Star Transport
-- statement:
--   Definitions and structural lemmas for RXPhysical Star Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXPhysicalStarTransport.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Mathlib.Tactic
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXPhysicalStarTransport
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXErrorPullback
open BDL26RZMap1CoordinateBridge BDL26RXXStarTransport
open BDL26RXLocalReplacement BDL26ReplacementSupport MultiscaleDecoder
open RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
def physicalXStar (P : TannerSquarePresentation) (x : P.X) : Finset P.Q :=
  Finset.univ.filter fun q => P.xq x q=true
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2=0)
def parentX (u : FamilyX S depth i.succ) : XCoord S i :=
  ((rxDegreeZeroEquiv S depth i h).symm u).1
def upperStar (u : FamilyX S depth i.succ) : Finset (FamilyQ S depth i.succ) :=
  physicalXStar (state S (i.val+1)).presentation u
def Localized (u : FamilyX S depth i.succ) (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ upperStar S depth i u
def Phi (u : FamilyX S depth i.succ) (a b : Upper S depth i) :=
  BDL26RXFiniteBlockTransport.Phi S depth i h {parentX S depth i h u} a b
def R (u : FamilyX S depth i.succ) (a b : Upper S depth i) :=
  BDL26RXFiniteBlockTransport.R S depth i h {parentX S depth i h u} a b
def L (u : FamilyX S depth i.succ) (a b : Upper S depth i) :=
  BDL26RXFiniteBlockTransport.L S depth i h {parentX S depth i h u} a b
def neighborZ (u : FamilyX S depth i.succ) : Finset (ZCoord S i) :=
  Finset.univ.filter fun z => ∃ q ∈ physicalXStar (state S i.val).presentation (parentX S depth i h u),
    (state S i.val).presentation.qz q z=true
def perturbationCenter (p : FamilyQ S depth i.succ) : FamilyX S depth i.succ :=
  ((state S (i.val+1)).admissible.toTannerSquareAdmissible.xqRoot p).1
def gradient (u : FamilyX S depth i.succ) : Upper S depth i :=
  (indexedFamily S depth).coboundary0 i.succ (canonicalBasisWord u)
def boundaryCenter (x : XCoord S i) : FamilyX S depth i.succ :=
  rxDegreeZeroEquiv S depth i h ⟨x,(0,(boundaryVertex S depth i x).val)⟩
theorem successor_state_eq (even : i.val % 2=0) :
    state S (i.val+1)=rxState S (state S i.val) := by
  change nextState S i.val (state S i.val)=_
  exact if_pos even
def upperQChart : RX1 (state S i.val).presentation S ≃ FamilyQ S depth i.succ :=
  Equiv.cast (congrArg (fun C : ConstructionState => C.presentation.Q)
    (successor_state_eq S depth i h)).symm
def verticalPhysical (x : XCoord S i) : FamilyQ S depth i.succ :=
  upperQChart S depth i h (Sum.inl ⟨x,Sum.inr (boundaryVertex S depth i x)⟩)
end QEC.Coding.BDL26RXPhysicalStarTransport


