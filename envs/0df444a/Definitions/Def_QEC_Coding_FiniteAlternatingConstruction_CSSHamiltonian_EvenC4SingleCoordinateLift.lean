-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4SingleCoordinateLift
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_EvenC4SingleCoordinateLift
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T06:32:58.558265+00:00
-- url     : https://prove2.me/theorems/c14519d8-d6d6-45f6-ba48-e3cf3e6eb8e4
-- title:
--   Even C4 Single Coordinate Lift
-- statement:
--   Definitions and structural lemmas for Even C4 Single Coordinate Lift, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/EvenC4SingleCoordinateLift.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_ActualFailureReadout
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26EvenC4SingleCoordinateLift
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26AlternatingCochain BDL26OwnerIncidenceMasks
open BDL26TransposedStoppedDecoder BDL26CSSHamiltonian
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual BDL26ActualFailureReadout
open BDL26RZMap1CoordinateBridge
open RXCoarseGraining RXCoarseGrainingData
open scoped Classical
abbrev F := BDL26Field
def topRZ : StepIndex 4 := ⟨3,by decide⟩
theorem topRZ_odd : ¬topRZ.val%2=0 := by decide
def rxInput4 (S : OddScale) (s : TopInput S 1) :
    (indexedFamily S 4).Syndrome (Fin.succ (2 : StepIndex 4)) :=
  ⟨s.val,by
    obtain ⟨a,ha⟩ := s.property
    refine ⟨a,?_⟩
    rw [indexedFamily_coboundary1] at ha
    rw [indexedFamily_coboundary1]
    exact ha⟩
def rxInput3 (S : OddScale) (s : TopInput S 1) :
    (indexedFamily S 3).Syndrome (Fin.succ (2 : StepIndex 3)) :=
  ⟨s.val,by
    obtain ⟨a,ha⟩ := s.property
    refine ⟨a,?_⟩
    rw [indexedFamily_coboundary1] at ha
    rw [indexedFamily_coboundary1]
    exact ha⟩
def headInput4 (S : OddScale) (s : TopInput S 2) :
    (indexedFamily S 4).Syndrome topRZ.succ :=
  ⟨s.val,by
    obtain ⟨a,ha⟩ := s.property
    refine ⟨a,?_⟩
    rw [indexedFamily_coboundary1] at ha
    rw [indexedFamily_coboundary1]
    exact ha⟩
def headOutput (S : OddScale) (s : TopInput S 2) :
    AssemblyStepOutput (indexedDecoderData S 4) topRZ :=
  actualStep S 4 topRZ (headInput4 S s)
def headWord (S : OddScale) (s : TopInput S 2) : Word F (Physical S 4) :=
  fun q => (headOutput S s).correction q
def coarseTop (S : OddScale) (s : TopInput S 2) : TopInput S 1 :=
  ⟨fun z => (headOutput S s).coarse.val z,by
    obtain ⟨a,ha⟩ := (headOutput S s).coarse.property
    refine ⟨a,?_⟩
    change (indexedFamily S 4).coboundary1 topRZ.castSucc a=_ at ha
    rw [indexedFamily_coboundary1] at ha
    rw [indexedFamily_coboundary1]
    exact ha⟩
def rx4Word (S : OddScale) (s : TopInput S 1) : Word F (Physical S 3) :=
  fun q => (actualStep S 4 (2 : StepIndex 4) (rxInput4 S s)).correction q
def rx3Word (S : OddScale) (s : TopInput S 1) : Word F (Physical S 3) :=
  fun q => (actualStep S 3 (2 : StepIndex 3) (rxInput3 S s)).correction q
def rx4Coarse (S : OddScale) (s : TopInput S 1) :
    Word F (state S 2).presentation.Z :=
  fun z => (actualStep S 4 (2 : StepIndex 4) (rxInput4 S s)).coarse.val z
def rx3Coarse (S : OddScale) (s : TopInput S 1) :
    Word F (state S 2).presentation.Z :=
  fun z => (actualStep S 3 (2 : StepIndex 3) (rxInput3 S s)).coarse.val z
def midInput4 (S : OddScale) (s : TopInput S 2) :
    (indexedFamily S 4).Syndrome (Fin.succ (2 : StepIndex 4)) :=
  ⟨fun z => (actualInputs S 2 s (1 : LevelIndex 2)).val z,by
    obtain ⟨a,ha⟩ := (actualInputs S 2 s (1 : LevelIndex 2)).property
    refine ⟨a,?_⟩
    change (indexedFamily S 4).coboundary1
      (LevelTwoHistory.physicalLevel (1 : LevelIndex 2)) a=_ at ha
    rw [indexedFamily_coboundary1] at ha
    rw [indexedFamily_coboundary1]
    exact ha⟩
def topInput3 (S : OddScale) (s : TopInput S 1) :
    (indexedFamily S 3).Syndrome (Fin.succ (2 : StepIndex 3)) :=
  ⟨fun z => (actualInputs S 1 s (TopIndex 1)).val z,by
    obtain ⟨a,ha⟩ := (actualInputs S 1 s (TopIndex 1)).property
    refine ⟨a,?_⟩
    change (indexedFamily S 3).coboundary1
      (LevelTwoHistory.physicalLevel (TopIndex 1)) a=_ at ha
    rw [indexedFamily_coboundary1] at ha
    rw [indexedFamily_coboundary1]
    exact ha⟩
def actualTopInput4 (S : OddScale) (s : TopInput S 2) :
    (indexedFamily S 4).Syndrome topRZ.succ :=
  ⟨fun z => (actualInputs S 2 s (TopIndex 2)).val z,by
    obtain ⟨a,ha⟩ := (actualInputs S 2 s (TopIndex 2)).property
    refine ⟨a,?_⟩
    change (indexedFamily S 4).coboundary1
      (LevelTwoHistory.physicalLevel (TopIndex 2)) a=_ at ha
    rw [indexedFamily_coboundary1] at ha
    rw [indexedFamily_coboundary1]
    exact ha⟩
def domainOfTop (S : OddScale) (n : Nat) (s : TopInput S n) :
    XSyndromeDomain S n :=
  ⟨s.val,by
    obtain ⟨a,ha⟩ := s.property
    refine ⟨a,?_⟩
    rw [indexedFamily_coboundary1] at ha
    exact ha⟩
def coarseInput (S : OddScale) (u : XSyndromeDomain S 2) :
    XSyndromeDomain S 1 := domainOfTop S 1 (coarseTop S (input S 2 u))
def lowerRZInput4 (S : OddScale) (u : XSyndromeDomain S 1) :
    (indexedFamily S 4).Syndrome topRZ.castSucc :=
  ⟨u.val,by
    obtain ⟨a,ha⟩ := u.property
    refine ⟨a,?_⟩
    rw [indexedFamily_coboundary1]
    exact ha⟩
def embeddedHeadInput4 (S : OddScale) (u : XSyndromeDomain S 1) :
    (indexedFamily S 4).Syndrome topRZ.succ :=
  BDL26RZDecoderAdapter.embeddedSyndrome S 4 topRZ (lowerRZInput4 S u)
def embedC3Input (S : OddScale) (u : XSyndromeDomain S 1) : XSyndromeDomain S 2 :=
  ⟨fun z => (embeddedHeadInput4 S u).val z,by
    obtain ⟨a,ha⟩ := (embeddedHeadInput4 S u).property
    refine ⟨a,?_⟩
    rw [indexedFamily_coboundary1] at ha
    exact ha⟩
def rzOldQCoordinate (S : OddScale) (q : Physical S 3)
    (v : BDL26TannerLocalRegularity.QDoubleCylinderVertex
      (transposePresentation (state S 3).presentation) q S) : Physical S 4 :=
  BDL26RZPhysicalStarTransport.physicalQ S 4 topRZ topRZ_odd q v
def indexedUpper (S : OddScale) (a : Word F (Physical S 4)) :
    (indexedFamily S 4).Correction topRZ.succ := fun q => a q
def physicalPotential (S : OddScale)
    (p : (indexedFamily S 4).Cochain0 topRZ.succ) :
    Word F (state S 4).presentation.X := fun x => p x
end QEC.Coding.BDL26EvenC4SingleCoordinateLift
end


