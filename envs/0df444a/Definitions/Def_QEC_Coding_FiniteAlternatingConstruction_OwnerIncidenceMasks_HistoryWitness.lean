-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
-- name    : QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T06:00:13.229942+00:00
-- url     : https://prove2.me/theorems/3ecb575d-2738-47a6-bf8e-6827f916b7b1
-- title:
--   History Witness
-- statement:
--   Definitions and structural lemmas for History Witness, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryWitness.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_History
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerParentObstruction
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
namespace QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerParentObstruction BDL26ReplacementSupport
open MultiscaleDecoder
open scoped Classical
noncomputable def witnessLower : (indexedFamily scaleFive 4).Syndrome (3 : LevelIndex 4) :=
  ⟨(indexedFamily scaleFive 4).coboundary1 (3 : LevelIndex 4) evidenceCorrection,
    ⟨evidenceCorrection, rfl⟩⟩
noncomputable def witnessUpper : (indexedFamily scaleFive 4).Syndrome (4 : LevelIndex 4) :=
  BDL26RZDecoderAdapter.embeddedSyndrome scaleFive 4 (3 : StepIndex 4) witnessLower
noncomputable def witnessTopOutput : AssemblyStepOutput (indexedDecoderData scaleFive 4) (3 : StepIndex 4) :=
  (actualAboveTwoSteps scaleFive 2).step 3 (by decide) witnessUpper
noncomputable def witnessNextOutput : AssemblyStepOutput (indexedDecoderData scaleFive 4) (2 : StepIndex 4) :=
  (actualAboveTwoSteps scaleFive 2).step 2 (by decide) witnessTopOutput.coarse
noncomputable def witnessTopOwner
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) :
    Vertex (state scaleFive 3).presentation :=
  (BDL26RZDecoderAdapter.rzData scaleFive 4 (3 : StepIndex 4) (by decide)).topCenter p
noncomputable def witnessTopComponentOwner
    (j : Fin witnessTopOutput.localComponents.length) : Vertex (state scaleFive 3).presentation :=
  Vertex.z (BDL26RZDecoderAdapter.componentOwner scaleFive 4 (3 : StepIndex 4)
    (by decide) witnessUpper j)
noncomputable def outputMarks {depth : Nat}
    {C0 C1 C2 : LevelIndex depth → Type}
    [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
    {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
    {V : Type} [Fintype V] [DecidableEq V]
    (O : AssemblyStepOutput D i) (synOwner : C2 i.succ → V)
    (pieceOwner : Fin O.localComponents.length → V) : Finset V :=
  Finset.univ.filter (fun v =>
    (∃ p, synOwner p = v ∧ O.input.val p ≠ 0) ∨
    (∃ j, pieceOwner j = v ∧ O.componentAt j ≠ 0) ∨
    (∃ j p, synOwner p = v ∧ O.componentCoboundaryAt j p ≠ 0))
noncomputable def witnessTopMarks :=
  outputMarks witnessTopOutput witnessTopOwner witnessTopComponentOwner
noncomputable def witnessNextOwner (p : FamilyZ scaleFive 4 (3 : LevelIndex 4)) :
    Vertex (state scaleFive 2).presentation :=
  BDL26RXDecoderAdapter.vertexEquiv (state scaleFive 2).presentation
    ((BDL26RXDecoderAdapter.rxData scaleFive 4 (2 : StepIndex 4) (by decide)).topCenter p)
noncomputable def witnessNextComponentOwner
    (j : Fin witnessNextOutput.localComponents.length) : Vertex (state scaleFive 2).presentation :=
  BDL26RXDecoderAdapter.vertexEquiv (state scaleFive 2).presentation
    (BDL26RXDecoderAdapter.componentOwner scaleFive 4 (2 : StepIndex 4)
      (by decide) witnessTopOutput.coarse j)
noncomputable def witnessNextMarks :=
  outputMarks witnessNextOutput witnessNextOwner witnessNextComponentOwner
noncomputable def witnessBaseCorrection := (actualBase scaleFive 2).decode witnessNextOutput.coarse
noncomputable def witnessBaseEntry :
    RecursiveBaseLevelCorrection (LevelTwoHistory.suffixData (indexedDecoderData scaleFive 4)) where
  input := witnessNextOutput.coarse
  correction := witnessBaseCorrection
  relation := ((actualBase scaleFive 2).rightInverse witnessNextOutput.coarse).symm
noncomputable def witnessUpperError : (indexedFamily scaleFive 4).Correction (4 : LevelIndex 4) :=
  ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map1 evidenceCorrection
end QEC.Coding.BDL26OwnerIncidenceMasks


