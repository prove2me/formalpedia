-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceSecondReadout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:59:51.052178+00:00
-- url     : https://prove2.me/theorems/c3c57a80-ed28-46bd-b583-f3ddc91c4935
-- title:
--   RXFace Second Readout
-- statement:
--   Definitions and structural lemmas for RXFace Second Readout, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/RXFaceSecondReadout.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_RXFaceEdgeTower
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RXFaceSecondReadout
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual
open BDL26RZMap1CoordinateBridge BDL26RXLocalReplacement BDL26RZLocalReplacement
open BDL26LevelTwoCode BDL26LevelTwoDistance BDL26TannerLocalRegularity
open BDL26TransposedStoppedDecoder MultiscaleDecoder PauliSymplectic
open BDL26CSSHamiltonian BDL26ActualFailureReadout BDL26RXDecoderAdapter
open scoped Classical BigOperators
def physicalInput (S : OddScale) (n : Nat) (e : Word F (Physical S (n+2))) :
    XSyndromeDomain S n := ⟨zSyndrome S (n+2) e,⟨e,rfl⟩⟩
def physicalReadout (S : OddScale) (n : Nat) (e : Word F (Physical S (n+2))) :=
  firstReadout S n (physicalInput S n e)
def witnessScale : OddScale := ⟨3,by decide,by decide⟩
def qPortWord (P : TannerSquarePresentation) (q : P.Q) (b : F) :
    Word F (QDoubleCylinderVertex P q witnessScale) := fun v =>
  match v.2 with
  | Sum.inl (Sum.inl _) => if v.1=0 then 0 else 1
  | _ => b
abbrev rxIndex : StepIndex 3 := ⟨2,by decide⟩
theorem rxIndex_even : rxIndex.val%2=0 := by decide
abbrev P := (state witnessScale 2).presentation
abbrev Data := BDL26RXDecoderAdapter.rxData witnessScale 3 rxIndex rxIndex_even
abbrev Lq := BDL26RXDecoderAdapter.rxLq witnessScale 3 rxIndex rxIndex_even
abbrev Syn := (indexedFamily witnessScale 3).Syndrome rxIndex.succ
def selectedQWord (sigma : Syn) (q : P.Q) :
    Word F (QDoubleCylinderVertex P q witnessScale) :=
  (wordEquiv (BDL26RXDecoderAdapter.qCorrectionEquiv P witnessScale q)).symm
    (restrictWordLinear (Lq.correctionRegion q)
      (RXCoarseGraining.RXCoarseGrainingData.cqComponentTotal Data sigma.val q))
abbrev Lx := BDL26RXDecoderAdapter.rxLx witnessScale 3 rxIndex rxIndex_even
def gradientError (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale)) :
    Word F (Physical witnessScale 3) :=
  xExtend P witnessScale x
    (wordLinearMapTranspose (doubleCylinderBoundary1 P x witnessScale) g)
def gradientInput (x : P.X) (g : Word F (DoubleCylinderVertex P x witnessScale)) : Syn :=
  BDL26RXErrorPullback.errorSyndrome witnessScale 3 rxIndex (gradientError x g)
def zCopyBit (z : P.Z) : F := if z.2.1=0 then 0 else 1
def splitPotential (x : P.X) : Word F (DoubleCylinderVertex P x witnessScale) := fun v =>
  match v.2 with
  | Sum.inl w => match w.1 with
    | Vertex.q _ => if v.1=0 then 0 else 1
    | Vertex.z z => zCopyBit z
    | Vertex.x _ => 0
  | _ => 0
def rootWord (x : P.X) : Word F P.Q := fun q =>
  if P.xq x q=true then
    selectedQWord (gradientInput x (splitPotential x)) q (0,Sum.inl (Sum.inl ()))
  else 0
abbrev One := RawOne witnessScale
abbrev OneA := (rxState witnessScale baseState).admissible
def rectangleEndEdge (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale)
    (c : BDL26FiniteTannerSquare.Two) : P.Q := Sum.inl ⟨z,Sum.inl (c,rect.1)⟩
theorem rectangleEndEdge_incident (z : One.Z)
    (rect : SubdivisionBoundaryEdge (transposePresentation One) z witnessScale) (c : BDL26FiniteTannerSquare.Two) :
    P.xq (BDL26RXFaceEdgeTower.faceOwner witnessScale z (Sum.inr rect))
      (rectangleEndEdge z rect c)=true := by
  change rzXQIncidence One OneA.toTannerSquareAdmissible witnessScale
    (Sum.inl (Sum.inl ⟨z,Sum.inr rect⟩)) (Sum.inl ⟨z,Sum.inl (c,rect.1)⟩)=true
  apply decide_eq_true
  refine ⟨rfl,?_⟩
  exact (doubleCylinderFaceEdgeMatrix_rectangle_eq_one_iff
    (transposePresentation One) z witnessScale _ rect).mpr
      ⟨(0,c),doubleCylinderRectangleBoundaryEdge_zero _ _ _ _ _⟩
def witnessOldFace : One.Face := Sum.inr (Sum.inr ((0 : BDL26FiniteTannerSquare.BaseFace),(0 : BDL26FiniteTannerSquare.Two)))
def witnessZ : One.Z := One.faceZ witnessOldFace
def faceBoundaryStarEdge (T : TannerSquarePresentation) (f : T.Face) :
    XStarBoundaryEdge T (T.faceX f) :=
  ⟨Sum.inr (faceQZEdge T f 0),by
    change decide (∃ g : T.Face,
      xStarFaceMember T (T.faceX f) g=true ∧
      decide (faceQZEdge T f 0=faceQZEdge T g 0 ∨
        faceQZEdge T f 0=faceQZEdge T g 1)=true)=true
    apply decide_eq_true
    refine ⟨f,?_,?_⟩
    · change decide (T.faceX f=T.faceX f)=true
      exact decide_eq_true rfl
    · exact decide_eq_true (Or.inl rfl)⟩
def witnessBoundaryStarEdge : XStarBoundaryEdge (transposePresentation One) witnessZ :=
  faceBoundaryStarEdge (transposePresentation One) witnessOldFace
def witnessRectangle : SubdivisionBoundaryEdge (transposePresentation One) witnessZ witnessScale :=
  subdivisionOriginalBoundaryEdge (transposePresentation One) witnessZ witnessScale
    witnessBoundaryStarEdge ⟨0,by decide⟩
end QEC.Coding.BDL26RXFaceSecondReadout


