-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
-- name    : QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:14:44.431673+00:00
-- url     : https://prove2.me/theorems/02fb703a-4283-4e58-a7d7-7109968ea33b
-- title:
--   RZPhysical Star Transport
-- statement:
--   Definitions and structural lemmas for RZPhysical Star Transport, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RZPhysicalStarTransport.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZFiniteBlockTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Mathlib.Tactic
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26RZPhysicalStarTransport
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26DecodingGraph BDL26IndexedDecoder BDL26RZLocalReplacement
open BDL26RZMap1CoordinateBridge BDL26ReplacementSupport BDL26ReplacementCochainMaps
open BDL26RZDecoderAdapter BDL26RZErrorPullback MultiscaleDecoder
open RZCoarseGraining RZCoarseGrainingData
open BDL26RZFiniteBlockTransport
open scoped Classical BigOperators
def physicalZStar (P : TannerSquarePresentation) (z : P.Z) : Finset P.Q :=
  Finset.univ.filter fun q => P.qz q z=true
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (odd : ¬i.val%2=0)
def upperZChart : RZZ (Old S depth i) S ≃ FamilyZ S depth i.succ :=
  (coord2 S depth i odd).symm
def upperQChart : RZQ (Old S depth i) S ≃ FamilyQ S depth i.succ :=
  (coord1 S depth i odd).symm
def parentZ (u : FamilyZ S depth i.succ) : (Old S depth i).Z :=
  (coord2 S depth i odd u).1
def upperStar (u : FamilyZ S depth i.succ) : Finset (FamilyQ S depth i.succ) :=
  physicalZStar (state S (i.val+1)).presentation u
def Q0 (u : FamilyZ S depth i.succ) : Finset (Old S depth i).Q :=
  physicalZStar (Old S depth i) (parentZ S depth i odd u)
def Zplus (u : FamilyZ S depth i.succ) : Finset (Old S depth i).Z :=
  Coordinates.zplus (Old S depth i) (Q0 S depth i odd u) {parentZ S depth i odd u}
def Localized (u : FamilyZ S depth i.succ) (a b : Upper S depth i) : Prop :=
  hammingSupport (a+b) ⊆ upperStar S depth i u
def qCentre (q : (Old S depth i).Q) (z : (Old S depth i).Z)
    (hqz : (Old S depth i).qz q z=true)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) : FamilyZ S depth i.succ :=
  upperZChart S depth i odd ⟨z,qToZDoubleCylinderVertex (Old S depth i)
    (state S i.val).admissible.toTannerSquareAdmissible q z hqz S v⟩
def physicalQ (q : (Old S depth i).Q)
    (v : QDoubleCylinderVertex (transposePresentation (Old S depth i)) q S) : FamilyQ S depth i.succ :=
  upperQChart S depth i odd (.inr ⟨q,v⟩)
def verticalPhysical (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    FamilyQ S depth i.succ := upperQChart S depth i odd (.inl ⟨z,Sum.inr v⟩)
def verticalCentre (z : (Old S depth i).Z)
    (v : SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) z S) :
    FamilyZ S depth i.succ := upperZChart S depth i odd ⟨z,(0,v.1)⟩
def retainedQ : (Old S depth i).Q :=
  (Old S depth i).faceQ (BDL26UniformHistoryObstruction.retainedFace S i.val) 0
def retainedZ : (Old S depth i).Z :=
  (Old S depth i).faceZ (BDL26UniformHistoryObstruction.retainedFace S i.val)
theorem retained_incidence : (Old S depth i).qz (retainedQ S depth i) (retainedZ S depth i)=true :=
  (Old S depth i).data.faceQ_qz (BDL26UniformHistoryObstruction.retainedFace S i.val) 0
def retainedBoundaryVertex :
    SubdivisionBoundaryVertex (transposePresentation (Old S depth i)) (retainedZ S depth i) S :=
  subdivisionOriginalBoundaryVertex (transposePresentation (Old S depth i)) (retainedZ S depth i) S
    ((transposeXStarBoundaryVertexEquiv (Old S depth i) (retainedZ S depth i)).symm
      (qToZBoundaryVertex (Old S depth i) (state S i.val).admissible.toTannerSquareAdmissible
        (retainedQ S depth i) (retainedZ S depth i) (retained_incidence S depth i) (.inl ())))
end QEC.Coding.BDL26RZPhysicalStarTransport


