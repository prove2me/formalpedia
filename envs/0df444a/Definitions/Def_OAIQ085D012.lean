-- Prove2me | Definitions.Def_OAIQ085D012
-- name    : OAIQ085D012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T16:02:55.006798+00:00
-- url     : https://prove2.me/theorems/53aab274-2117-4821-8792-a26aaaa5f73b
-- title:
--   Definitions bundle OAIQ085D012 of the split of OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DirectedFeedback.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of directed feedback vertex set (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1030 declarations of OpenAI's Lean: 528 definitions, 5 inductive types or structures, 9 instances and 488 theorems. The definitions and types are `OAI.DFVSGames.Appendix.CompressionCount.Parameters`, `OAI.DFVSGames.Appendix.CompressionCount.base`, `OAI.DFVSGames.Appendix.CompressionCount.compress`, `OAI.DFVSGames.Appendix.CompressionCount.graph`, `OAI.DFVSGames.Appendix.CompressionCount.lift`, `OAI.DFVSGames.Appendix.CompressionCount.lower`, `OAI.DFVSGames.Decoder.ActualSeedEvents.Datum`, `OAI.DFVSGames.Decoder.MatrixCoordinates.changeDomain`, `OAI.DFVSGames.Decoder.MatrixCoordinates.domainCoordinates`, `OAI.DFVSGames.Decoder.MatrixCoordinates.functionalEquiv`, `OAI.DFVSGames.Decoder.MatrixCoordinates.mapEquiv`, `OAI.DFVSGames.Explicit.MachineClone100Cleanup.clearFields`, `OAI.DFVSGames.Explicit.MachineClone100Context.contextTapes`, `OAI.DFVSGames.Explicit.MachineClone100Headers.resultTapes`, `OAI.DFVSGames.Explicit.MachineClone100Model.affineEmit`, `OAI.DFVSGames.Explicit.MachineClone100Model.emission`, `OAI.DFVSGames.Explicit.MachineSingleOrbitCodec.doubledRowBits`, `OAI.DFVSGames.Explicit.MachineSingleOrbitCodec.doubledRowsBits`, `OAI.DFVSGames.Explicit.MachineSingleOrbitCodec.rowBits`, `OAI.DFVSGames.Explicit.MachineSingleOrbitCodec.rowsBits`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Buffer`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.Ambient`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.Plan`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.emittedTapes`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.endpointTapes`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.finishTapes`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.headerResultTapes`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.inputStream`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.preparedTapes`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.rowOperands`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.rowRelation`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.rowRest`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFMachine.Program.rowResultTapes`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFPattern.labelEquiv`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFPattern.labelIndex`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFPattern.patternRelationIndex`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFPattern.relationAddress`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFPattern.tableGraph`, `OAI.DFVSGames.Foundations.Complexity.FinalCNFTableAdapter.genericRow` and 493 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `DirectedFeedback_Encoding_Bounds`, `DirectedFeedback_Encoding_CanonicalWordTemplate`, `DirectedFeedback_Encoding_EmitRows`, `DirectedFeedback_Encoding_ExpanderTableWords`, `DirectedFeedback_Encoding_FinalCNFPattern`, `DirectedFeedback_Encoding_Lookup`, `DirectedFeedback_Encoding_Occurrences`, `DirectedFeedback_Encoding_PortTables`, `DirectedFeedback_Encoding_PreprocessingRegularTables`, `DirectedFeedback_Encoding_PreprocessingRegularWords`, `DirectedFeedback_Encoding_PreprocessingStageMaps`, `DirectedFeedback_Encoding_SelectedPolicies`, `DirectedFeedback_Encoding_VerifierCNF`, `DirectedFeedback_Games_AddressTupleBody`, `DirectedFeedback_Games_AddressTupleLoaded`, `DirectedFeedback_Games_AffineWitnessNormalization`, `DirectedFeedback_Games_ExpanderFamily`, `DirectedFeedback_Games_Game`, `DirectedFeedback_Games_Generator`, `DirectedFeedback_Games_GeneratorModel`, `DirectedFeedback_Games_InitialGraph`, `DirectedFeedback_Games_LocalEquation`, `DirectedFeedback_Games_Overlay`, `DirectedFeedback_Games_Parameters`, `DirectedFeedback_Games_PoweringFinalConstants`, `DirectedFeedback_Games_PoweringReach`, `DirectedFeedback_Games_Product`, `DirectedFeedback_Games_SignaturePrepare`, `DirectedFeedback_Games_Target`, `DirectedFeedback_Games_TestEmit`, `DirectedFeedback_Games_TupleBody`, `DirectedFeedback_Games_UniformReduction`, `DirectedFeedback_Machines_ContextClear`, `DirectedFeedback_Machines_FinalCNFHeader`, `DirectedFeedback_Machines_FinalCNFStream`, `DirectedFeedback_Machines_GraphCounterFinish`, `DirectedFeedback_Machines_LoopInit`, `DirectedFeedback_Machines_MachineAddressHeaders`, `DirectedFeedback_Machines_MachineAffineLookup`, `DirectedFeedback_Machines_MachineCloudCount`, `DirectedFeedback_Machines_MachineCloudPadding`, `DirectedFeedback_Machines_MachineCloudSelect`, `DirectedFeedback_Machines_MachineDummyRows`, `DirectedFeedback_Machines_MachineExpanderFamilyLoop`, `DirectedFeedback_Machines_MachineExpanderFamilyTapes`, `DirectedFeedback_Machines_MachineExpanderRow`, `DirectedFeedback_Machines_MachineExpanderRowDivision`, `DirectedFeedback_Machines_MachineExpanderRowLookup`, `DirectedFeedback_Machines_MachineExpanderTableLoop`, `DirectedFeedback_Machines_MachineLookupSpec`, `DirectedFeedback_Machines_MachineOutcomeRows`, `DirectedFeedback_Machines_MachinePaddedExpanderFamily`, `DirectedFeedback_Machines_MachinePreservingLookupClean`, `DirectedFeedback_Machines_MachineRegularMetadata`, `DirectedFeedback_Machines_MachineRegularOriginalBody`, `DirectedFeedback_Machines_MachineSingleOrbitBridge`, `DirectedFeedback_Machines_MachineSingleOrbitCodec`, `DirectedFeedback_Machines_MachineStateEquiv`, `DirectedFeedback_Machines_MachineTuple`, `DirectedFeedback_Machines_PoweringMachineLoop`, `DirectedFeedback_Machines_PoweringMachineOuterLoop`, `DirectedFeedback_Machines_PoweringMachineRelationField`, `DirectedFeedback_Machines_PoweringMachineRowBody`, `DirectedFeedback_Machines_PoweringMachineWord`, `DirectedFeedback_Machines_RawInitialMachineFinish`, `DirectedFeedback_Machines_RawInitialMachineStart`, `DirectedFeedback_Probability_PoweringFieldPlan`, `DirectedFeedback_RankGraph_Clone100Counting`, `DirectedFeedback_RankGraph_MachineClone100Cleanup`.
--
--   **Imports.** It imports the bundles `OAIQ085D006` and `OAIQ085D007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ085D018`, `OAIQ085D019`, `OAIQ085D020`, `OAIQ085D021`, `OAIQ085D022` and `OAIQ085D023`.
-- source:
--   OpenAI, Constant-factor hardness of directed feedback vertex set (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-directed-feedback-vertex-set-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ085D006
import Definitions.Def_OAIQ085D007

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def localInstruction (source : K) (labels : Unit → Λ) (exit : Option Λ) (_ : Unit) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineDrain.drain source (labels ()) exit

def instruction (chosen : List K) (labels : Label chosen → Λ) (exit : Option Λ) :
    Label chosen → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineFiniteSequence.instruction (LocalLabel (K := K)) (fun _ => ())
    localInstruction chosen labels exit

end DFVSGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def program (index source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard index .skip .select
  | .skip => discard source .skip .guard
  | .select => select source destination .copy .rejected
  | .copy => Hastad.SourceMachine.fieldLoop source destination .copy (some .accepted)
  | .accepted => .halt
  | .rejected => .halt

end DFVSGames.Foundations.Complexity.MachineLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineLookupSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false .copySecond (some (.lookup .guard))
  | .lookup l => MachineSubroutine.statement Label.lookup none
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

end DFVSGames.Foundations.Complexity.MachinePreservingLookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Occurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceOccurrences

open DFVSGames.Reduction.CloneGap
open scoped BigOperators


open SourceContexts
open DFVSGames.Reduction.FiniteNoise

theorem sourceList_empty (F : Target.Formula) (u D : ℕ) (h : F.clauses = []) :
    sourceList F u D = [emptyFormulaEquation F u] := by simp [sourceList, h]

theorem sourceList_nonempty (F : Target.Formula) (u D : ℕ) (h : F.clauses ≠ []) :
    sourceList F u D = rawSourceList F u D := by
  unfold sourceList
  rw [List.isEmpty_eq_false_iff.mpr h]
  rfl

theorem sourceList_ne_nil (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    sourceList F u D ≠ [] := by
  by_cases h : F.clauses = []
  · rw [sourceList_empty F u D h]
    simp
  · rw [sourceList_nonempty F u D h]
    apply List.length_pos_iff.mp
    rw [rawSourceList_length]
    have hc : 0 < F.clauses.length := List.length_pos_iff.mpr h
    positivity

def sourceInput (F : Target.Formula) (u D : ℕ) (hD : 0 < D) :
    DFVSGames.Reduction.SourceEncoding.Input :=
  ⟨nBits F u, sourceList F u D, sourceList_ne_nil F u D hD⟩


end DFVSGames.Foundations.Hastad.SourceOccurrences


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceProfileBridge

open Target SourceContexts SourceOccurrences SourceLocalSignature
open Complexity

def positionEncoding (u : ℕ) : Encoding (Position u) :=
  (Encoding.fin u).prod slotEncoding

def names (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → ℕ :=
  fun i => (occurrenceName F c ((positionEncoding u).code.symm i)).val

def nameWords (F : Formula) {u : ℕ} (c : ClauseContext F u) :
    Fin (positionEncoding u).size → List Bool :=
  fun i => encodeWord (names F c i)

end DFVSGames.Foundations.Hastad.SourceProfileBridge


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAffineLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachineAffineLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

inductive Label
  | seed | scan | restore | copyFirst | copySecond
  | lookup (l : MachineLookup.Label)
  deriving DecidableEq, Fintype

def instruction (source : K) (tape : Fin 5 → K) (coefficient offset : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed (tape 1) offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source (tape 4) (tape 1)
      coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt (tape 4) source id false
      (labels .restore) (some (labels .copyFirst))
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false
      (labels .copySecond) (some (labels (.lookup .guard)))
  | .lookup l => MachineSubroutine.statement (fun q => labels (.lookup q)) exit
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

end DFVSGames.Foundations.Complexity.MachineAffineLookup


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_LocalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open DFVSGames.Reduction.CloneGap
open DFVSGames.Reduction.FiniteNoise

abbrev LocalInput (u D : ℕ) := Signature u × SourceTape.TestTape (I u) (J u) D

end DFVSGames.Foundations.Hastad.SourceLocalEquation


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_TestEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceTestEmit

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open DFVSGames.Reduction.CloneGap
open Complexity

abbrev State (u D : ℕ) := LocalInput u D × Option Bool

end DFVSGames.Foundations.Hastad.SourceTestEmit


namespace DFVSGames.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceTestEmit

abbrev State (u D : Nat) := SourceTestEmit.State u D

end DFVSGames.Foundations.Hastad.SourceTestAppend


namespace DFVSGames.Foundations.Hastad.SourceQueryLoop

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

abbrev Query (u D : Nat) := SourceTape.TestTape (I u) (J u) D
abbrev State (u D : Nat) := SourceTestAppend.State u D

end DFVSGames.Foundations.Hastad.SourceQueryLoop


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Game
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceHonest

open DFVSGames.Reduction.CloneGap
open DFVSGames.Reduction.FiniteNoise
open scoped BigOperators


open SourceContexts
open SourceOccurrences

def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun c => honestJ F c assignment)

def honestBits (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) : Fin (nBits F u) → Bool :=
  assignmentOfKey (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
    (jEncoding u) (honestGlobal F u assignment)

@[simp] theorem honestBits_code (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool)
    (key : GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :
    honestBits F u assignment ((proofEncoding F u).code key) =
      honestGlobal F u assignment key :=
  assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u)
    (iEncoding u) (jEncoding u) (honestGlobal F u assignment) key

@[simp] theorem honestBits_dummy (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    honestBits F u assignment (dummyIndex F u) = false := by
  rw [dummyIndex, honestBits_code]
  rfl


end DFVSGames.Foundations.Hastad.SourceHonest


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_SignaturePrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open DFVSGames.Foundations.Complexity

abbrev Width (u : ℕ) := (positionEncoding u).size
abbrev ProfileState (u : ℕ) := MachineCompare.State (MachineFieldProfile.Profile (Width u))
abbrev State (u : ℕ) (τ : Type) := ProfileState u × (Signature u × τ)

variable {u : ℕ} {Extra τ : Type}

def variableField (p : Position u) : Arena u Extra :=
  SourceContextLoad.variableField p.1 (slotEncoding.code p.2)

def place : MachineFieldProfile.Tape (Width u) → Arena u Extra
  | .inl i => variableField ((positionEncoding u).code.symm i)
  | .inr w => if w = 0 then .index else if w = 1 then .work else .scratch

def unplace : Arena u Extra → Option (MachineFieldProfile.Tape (Width u))
  | .index => some (.inr 0)
  | .work => some (.inr 1)
  | .scratch => some (.inr 2)
  | .field t s =>
    if s = 0 then some (.inl ((positionEncoding u).code (t, .first)))
    else if s = 2 then some (.inl ((positionEncoding u).code (t, .second)))
    else if s = 4 then some (.inl ((positionEncoding u).code (t, .third))) else none
  | _ => none

@[simp] theorem unplace_place (k : MachineFieldProfile.Tape (Width u)) :
    unplace (place (Extra := Extra) k) = some k := by
  cases k with
  | inl i =>
    obtain ⟨p, rfl⟩ := (positionEncoding u).code.surjective i
    rcases p with ⟨t, s⟩
    simp only [place, Equiv.symm_apply_apply]
    cases s <;> rfl
  | inr w =>
    obtain ⟨w, hw⟩ := w
    have h : w = 0 ∨ w = 1 ∨ w = 2 := by omega
    rcases h with rfl | rfl | rfl <;> rfl

theorem place_unplace (a : Arena u Extra) (k : MachineFieldProfile.Tape (Width u))
    (h : unplace a = some k) : place k = a := by
  cases a with
  | formula => simp [unplace] at h
  | index => cases Option.some.inj h; rfl
  | work => cases Option.some.inj h; rfl
  | scratch => cases Option.some.inj h; rfl
  | copyScratch => simp [unplace] at h
  | current t => simp [unplace] at h
  | remaining t => simp [unplace] at h
  | extra e => simp [unplace] at h
  | field t s =>
    by_cases h0 : s = 0
    · subst s
      simp only [unplace, ↓reduceIte] at h
      cases Option.some.inj h
      simp only [place, Equiv.symm_apply_apply]
      rfl
    · by_cases h2 : s = 2
      · subst s
        simp only [unplace, ↓reduceIte] at h
        cases Option.some.inj h
        simp only [place, Equiv.symm_apply_apply]
        rfl
      · by_cases h4 : s = 4
        · subst s
          simp only [unplace, ↓reduceIte] at h
          cases Option.some.inj h
          simp only [place, Equiv.symm_apply_apply]
          rfl
        · simp [unplace, h0, h2, h4] at h

def fill (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool) : Arena u Extra → List Bool :=
  fun a => match unplace a with
    | some k => localTapes k
    | none => base a

@[simp] theorem fill_place (base : Arena u Extra → List Bool)
    (localTapes : MachineFieldProfile.Tape (Width u) → List Bool)
    (k : MachineFieldProfile.Tape (Width u)) : fill base localTapes (place k) = localTapes k := by
  simp only [fill, unplace_place]

@[simp] theorem fill_self (base : Arena u Extra → List Bool) :
    fill base (base ∘ place) = base := by
  funext a
  cases h : unplace a with
  | none => simp only [fill, h]
  | some k =>
    simp only [fill, h, Function.comp_apply, place_unplace a k h]

end DFVSGames.Foundations.Hastad.SourceSignaturePrepare


namespace DFVSGames.Foundations.Hastad.SourceContextPrepare

open Turing DFVSGames.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

abbrev PrepareState (u : Nat) (τ : Type) := SourceSignaturePrepare.State u τ
abbrev State (u : Nat) (τ : Type) := LoadState × PrepareState u τ

variable {u : Nat} {Extra τ : Type}

variable [DecidableEq Extra]

def initialState (initialProfile : MachineFieldProfile.Profile (SourceSignaturePrepare.Width u))
    (initial : Signature u) (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState initialProfile, (initial, ambient)))

def finalState (F : Formula) (c : ClauseContext F u) (selected : SlotContext u)
    (ambient : τ) : State u τ :=
  (((), none), (MachineFieldProfile.normalState (MachineFieldProfile.equalityProfile (nameWords F c)),
    (ofContext F c selected, ambient)))

end DFVSGames.Foundations.Hastad.SourceContextPrepare

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_LoopInit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

abbrev QueryState (u D : Nat) := SourceQueryLoop.State u D
abbrev State (u D : Nat) := SourceContextPrepare.State u (QueryState u D × ArithmeticState)
abbrev QueryMetadata (u : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × ArithmeticState))
abbrev ArithmeticMetadata (u D : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × QueryState u D))

variable {u D : Nat} {Extra : Type}

def canonicalSignature (u : Nat) : Signature u :=
  ⟨fun _ => false, fun _ _ => false, fun _ => .first⟩

def canonicalState (initialQuery : SourceQueryLoop.Query u D) : State u D :=
  SourceContextPrepare.initialState (fun _ _ => false) (canonicalSignature u)
    (((canonicalSignature u, initialQuery), none), (((), ()), none))

def queryStateEquiv (u D : Nat) : QueryState u D × QueryMetadata u ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.1, x.2.2.2.2))))
  invFun x := (x.2.2.2.1, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def arithmeticStateEquiv (u D : Nat) : ArithmeticState × ArithmeticMetadata u D ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.2.2.2.2, x.1))))
  invFun x := (x.2.2.2.2, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.1))))
  left_inv _ := rfl
  right_inv _ := rfl

end DFVSGames.Foundations.Hastad.SourceRuntimeModel

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_GeneratorModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel

abbrev State (u D : Nat) := SourceRuntimeModel.State u D

abbrev ControlAmbient (u D : Nat) := (Unit × Unit) × ArithmeticMetadata u D

def controlStateEquiv (u D : Nat) :
    ControlAmbient u D × Option Bool ≃ State u D where
  toFun x := arithmeticStateEquiv u D ((x.1.1, x.2), x.1.2)
  invFun x :=
    let y := (arithmeticStateEquiv u D).symm x
    ((y.1.1, y.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def initialQuery (u D : Nat) (hD : 0 < D) : SourceQueryLoop.Query u D :=
  (fun _ => false, fun _ => ⟨0, hD⟩, fun _ => false)

def initialState (u D : Nat) (hD : 0 < D) : State u D :=
  canonicalState (initialQuery u D hD)

def initialAmbient (u D : Nat) (hD : 0 < D) : ControlAmbient u D :=
  ((controlStateEquiv u D).symm (initialState u D hD)).1

end DFVSGames.Foundations.Hastad.SourceGeneratorModel


namespace DFVSGames.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.DFVSGames.Foundations.Hastad.SourceStartup.generatorModelExtraDecidableEq
@[simp] theorem ready_field (F : Target.Formula) (j : Fin u) (s : Fin 6) :
    readyTapes (D := D) F (.field j s) = [] := initialized_field F j s

@[simp] theorem ready_sharedWork (F : Target.Formula) :
    readyTapes (u := u) (D := D) F .work = [] := by
  simp [readyTapes, initializedTapes]

end

end DFVSGames.Foundations.Hastad.SourceStartup


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_ContextClear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceContextClear

open Turing Complexity MachineComposition

abbrev Tape := SourceContextLoad.Tape

variable {u : Nat} {Extra : Type}

def fieldAt (i : Fin (u * 6)) : Tape u Extra :=
  .field (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

def fields : List (Tape u Extra) := List.ofFn fieldAt

@[simp] theorem fields_length : (fields (u := u) (Extra := Extra)).length = 6 * u := by
  simp [fields, Nat.mul_comm]

def outputTapes (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .field _ _ => []
  | p => base p

@[simp] theorem output_field (base : Tape u Extra → List Bool) (j : Fin u) (s : Fin 6) :
    outputTapes base (.field j s) = [] := rfl

end DFVSGames.Foundations.Hastad.SourceContextClear


namespace DFVSGames.Foundations.Hastad.SourceTupleTape

open Turing Complexity SourceContexts SourceRuntimeModel

variable {u : Nat} {Extra : Type}

def tapes (base : Arena u Extra → List Bool) (s : Snapshot) : Arena u Extra → List Bool
  | .extra (.inr .rank) => s.rank
  | .extra (.inr .rightBase) => s.rightBase
  | .extra (.inr .leftBase) => s.leftBase
  | .extra (.inr .zero) => s.zero
  | .extra (.inr .accumulator) => s.emitted.reverse ++ base (workTape .accumulator)
  | k => base k

@[simp] theorem tapes_rank (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rank) = s.rank := rfl
@[simp] theorem tapes_rightBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .rightBase) = s.rightBase := rfl
@[simp] theorem tapes_leftBase (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBase) = s.leftBase := rfl
@[simp] theorem tapes_zero (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .zero) = s.zero := rfl
@[simp] theorem tapes_accumulator (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .accumulator) = s.emitted.reverse ++ base (workTape .accumulator) := rfl
@[simp] theorem tapes_coefficient (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .coefficient) = base (workTape .coefficient) := rfl
@[simp] theorem tapes_dummy (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .dummy) = base (workTape .dummy) := rfl
@[simp] theorem tapes_leftBlock (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .leftBlock) = base (workTape .leftBlock) := rfl
@[simp] theorem tapes_queryTemporary (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryTemporary) = base (workTape .queryTemporary) := rfl
@[simp] theorem tapes_queryScratch (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s (workTape .queryScratch) = base (workTape .queryScratch) := rfl
@[simp] theorem tapes_field (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) (k : Fin 6) :
    tapes base s (.field j k) = base (.field j k) := rfl
@[simp] theorem tapes_current (base : Arena u Extra → List Bool) (s : Snapshot) (j : Fin u) :
    tapes base s (.current j) = base (.current j) := rfl
@[simp] theorem tapes_formula (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .formula = base .formula := rfl
@[simp] theorem tapes_index (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .index = base .index := rfl
@[simp] theorem tapes_work (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s .work = base .work := rfl
@[simp] theorem tapes_variableHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s variableHeader = base variableHeader := rfl
@[simp] theorem tapes_clauseHeader (base : Arena u Extra → List Bool) (s : Snapshot) :
    tapes base s clauseHeader = base clauseHeader := rfl

end DFVSGames.Foundations.Hastad.SourceTupleTape

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_TupleBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Hastad.SourceTupleBody

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape

abbrev SlotCount (u : Nat) := (slotContextEncoding u).size
abbrev Query (u D : Nat) := SourceQueryLoop.Query u D

variable {u D : Nat} {Extra : Type}

def selected (index : Fin (SlotCount u)) : SlotContext u :=
  (slotContextEncoding u).code.symm index

variable [DecidableEq Extra]

def selectState (initialQuery : Query u D) (index : Fin (SlotCount u))
    (state : State u D) : State u D :=
  (state.1, (state.2.1, (state.2.2.1,
    ((({state.2.2.1 with selected := selected index}, initialQuery), none), state.2.2.2.2))))

def contextSignature (F : Target.Formula) (c : ClauseContext F u) : Signature u :=
  ofContext F c (fun _ => .first)

def workingState (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) : State u D :=
  SourceContextPrepare.finalState F c (fun _ => .first)
    (((signature, query), none), (((), ()), none))

@[simp] theorem workingState_loader (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    (((), none), (workingState F c signature query).2) = workingState F c signature query := rfl

def arithmeticMetadata (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) : ArithmeticMetadata u D :=
  (((), none), (MachineFieldProfile.normalState
    (MachineFieldProfile.equalityProfile (SourceProfileBridge.nameWords F c)),
      (contextSignature F c, ((signature, query), none))))

def queryMetadata (F : Target.Formula) (c : ClauseContext F u) : QueryMetadata u :=
  (((), none), (MachineFieldProfile.normalState
    (MachineFieldProfile.equalityProfile (SourceProfileBridge.nameWords F c)),
      (contextSignature F c, (((), ()), none))))

@[simp] theorem arithmeticState_working (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    arithmeticStateEquiv u D ((((), ()), none), arithmeticMetadata F c signature query) =
      workingState F c signature query := rfl

@[simp] theorem queryState_working (F : Target.Formula) (c : ClauseContext F u)
    (signature : Signature u) (query : Query u D) :
    queryStateEquiv u D (((signature, query), none), queryMetadata F c) =
      workingState F c signature query := rfl

@[simp] theorem select_workingState (F : Target.Formula) (c : ClauseContext F u)
    (index : Fin (SlotCount u)) (initialQuery query : Query u D) (signature : Signature u) :
    selectState initialQuery index (workingState F c signature query) =
      workingState F c (ofContext F c (selected index)) initialQuery := rfl

omit [DecidableEq Extra] in
@[simp] theorem loaded_extra (F : Target.Formula) (c : ClauseContext F u)
    (base : Arena u Extra → List Bool) (extra : BodyExtra Extra) :
    SourceContextLoad.stageTapes F c base u (.extra extra) = base (.extra extra) :=
  SourceContextLoad.stageTapes_frame F c base u _ (by simp) (by simp) (by simp)

end DFVSGames.Foundations.Hastad.SourceTupleBody

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Hastad.SourceGeneratorProgram

open Turing Complexity SourceGeneratorModel

noncomputable section

abbrev Ambient (u D : Nat) := SourceGeneratorModel.ControlAmbient u D
abbrev State (u D : Nat) := Ambient u D × Option Bool

local instance instDecidableEqExtra_rfda2c4_1 (u D : Nat) : DecidableEq (Extra u D) := Classical.decEq _
def sourceStateEquiv (u D : Nat) : SourceRuntimeModel.State u D × Unit ≃ State u D where
  toFun x := (controlStateEquiv u D).symm x.1
  invFun x := (controlStateEquiv u D x, ())
  left_inv x := by cases x with | mk x y => cases y; simp
  right_inv x := by simp

end

end DFVSGames.Foundations.Hastad.SourceGeneratorProgram

namespace DFVSGames.Foundations.Hastad.SourceGeneratorTraversal

open Turing Complexity SourceContexts SourceOccurrences SourceRuntimeModel
open SourceGeneratorModel SourceGeneratorProgram SourceOdometerSchedule

noncomputable section

variable {u D : Nat}

local instance instDecidableEqExtra (u D : Nat) : DecidableEq (SourceGeneratorModel.Extra u D) := Classical.decEq _

def accumulatorRole (u D : Nat) : BodyExtra (SourceGeneratorModel.Extra u D) :=
  .inr .accumulator

def leafTapes (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    SourceGeneratorModel.Tape u D → List Bool :=
  setDigits F.clauses.length (fun i => (c i).val)
    (setAcc (accumulatorRole u D) (SourceStartup.readyTapes F) output)

@[simp] theorem leaf_accumulator (F : Target.Formula) (c : ClauseContext F u) (output : List Bool) :
    leafTapes (D := D) F c output (accumulatorTape u D) = output := by
  exact setAcc_apply (accumulatorRole u D) (SourceStartup.readyTapes F) output

@[simp] theorem source_initial (hD : 0 < D) :
    sourceStateEquiv u D (canonicalState (initialQuery u D hD), ()) =
      (initialAmbient u D hD, none) := rfl

def traversalOutput (F : Target.Formula) (hD : 0 < D) : SourceGeneratorModel.Tape u D → List Bool :=
  Function.update (SourceStartup.readyTapes F) (accumulatorTape u D)
    (DFVSGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse

@[simp] theorem traversalOutput_accumulator (F : Target.Formula) (hD : 0 < D) :
    traversalOutput F hD (accumulatorTape u D) =
      (DFVSGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  simp [traversalOutput]

end

end DFVSGames.Foundations.Hastad.SourceGeneratorTraversal

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Generator
attribute [-instance] _root_.OAI.DFVSGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.GraphTables

open DFVSGames.Foundations.Complexity

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ Label) : Table :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

end DFVSGames.Foundations.PCP.GraphTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PortTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PortTables

open PoweringWalks

variable {n d : Nat}

theorem flatRows_valid (table : Table n d) : GraphTables.Valid (flatRows table) := by
  constructor
  · intro i
    simpa only [reverseAt_flatRows] using table.involutive i
  · intro i a b
    simpa only [reverseAt_flatRows, acceptsAt_flatRows] using table.transpose i a b

def graphTable (table : Table n d) : GraphTables.Table :=
  ⟨n, n * d, flatRows table, flatRows_valid table⟩

def tableBits (table : Table n d) : List Bool := GraphTables.tableBits (graphTable table)

end DFVSGames.Foundations.PCP.PortTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def stepGraph {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    PortGraph (Fin (v * ((d * d) * (d * d)))) (Fin (d * d)) :=
  GraphTransport.reindex
    (ZigzagGraphs.zigzag (ZigzagGraphs.square (graph G))
      (GraphTransport.reindex (graph H) (rowIndex (d * d) (d * d)).symm (Equiv.refl _)))
    (vertexIndex v (d * d)) (rowIndex d d)

def step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    Table (v * ((d * d) * (d * d))) (d * d) := ofGraph (stepGraph G H)

def stepLookup {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d)
    (x : Fin (v * ((d * d) * (d * d))) × Fin (d * d)) :
    Fin (v * ((d * d) * (d * d))) × Fin (d * d) :=
  let vc := (rowIndex v ((d * d) * (d * d))).symm x.1
  let ports := (rowIndex d d).symm x.2
  let first := lookup H (vc.2, ports.1)
  let squarePorts := (rowIndex (d * d) (d * d)).symm first.1
  let outerFirst := lookup G (vc.1, squarePorts.1)
  let outerSecond := lookup G (outerFirst.1, squarePorts.2)
  let last := lookup H (rowIndex (d * d) (d * d) (outerSecond.2, outerFirst.2), ports.2)
  (rowIndex v ((d * d) * (d * d)) (outerSecond.1, last.1),
    rowIndex d d (last.2, first.2))

theorem lookup_step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d)
    (x : Fin (v * ((d * d) * (d * d))) × Fin (d * d)) :
    lookup (step G H) x = stepLookup G H x := by
  simp [step, stepGraph, GraphTransport.reindex,
    Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm, Equiv.refl_apply, vertexIndex, Equiv.apply_symm_apply,
    ZigzagGraphs.zigzag, ZigzagGraphs.square, ZigzagGraphs.involutionEquiv,
    ZigzagGraphs.cloudFirst, ZigzagGraphs.crossCloud,
    graph_rot,
    stepLookup, Prod.map, Equiv.symm_symm]
  all_goals repeat' constructor

def initial (d : Nat) : Table 1 (d * d) :=
  ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

def family {d : Nat} (H : Table ((d * d) * (d * d)) d) :
    (n : Nat) → Table (vertexCount (d * d) n) (d * d)
  | 0 => initial d
  | n + 1 => step (family H n) H

end DFVSGames.Foundations.PCP.ExpanderTables


namespace DFVSGames.Foundations.PCP.PreprocessingLevels

@[simp] theorem boundedLevel_zero : boundedLevel 0 = 0 := rfl

@[simp] theorem paddedSize_zero : paddedSize 0 = 1 := rfl

end DFVSGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingRegularTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem reverseIndex_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).reverseIndex[rowIndex m d (v.castLE h, p)] =
      rowIndex m d ((rotation table (v, p)).1.castLE h, (rotation table (v, p)).2) := by
  rw [← rowIndex_rotation, rotation_pad_old]

theorem relation_ext_inline_PreprocessingPaddingTables {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

theorem relations_pad_old (table : Table n d) (h : n ≤ m)
    (v : Fin n) (p : Fin d) :
    (pad table h).relations[rowIndex m d (v.castLE h, p)] =
      table.relations[rowIndex n d (v, p)] := by
  apply relation_ext_inline_PreprocessingPaddingTables
  intro a b
  exact accepts_pad_old table h v p a b

end DFVSGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open DFVSGames.Foundations.PCP

variable {σ : Type}

def program (g : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push .power (fun _ => false) (.push .power (fun _ => true)
      (.push .level (fun _ => false) (.goto fun _ => .fuelFirst)))
  | .fuelFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .fuelFirst (some .fuelSecond)
  | .fuelSecond => MachineCopy.forkLoop
      .spare .input .fuel false .fuelSecond (some .guard)
  | .guard => MachineUnaryCounter.guard .fuel .copyFirst .cleanup
  | .copyFirst => Reduction.MachineTransfer.loopAt
      .input .spare id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop
      .spare .input .work false .copySecond (some .compare)
  | .compare => compareLoop
  | .restore => Reduction.MachineTransfer.loopAt
      .saved .power id false .restore (some .decide)
  | .decide => .branch (fun state => state.1.2)
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .scale))
      (.load (fun state => ((state.1.1, false), none)) (.goto fun _ => .cleanup))
  | .scale => scaleLoop g
  | .transfer => Reduction.MachineTransfer.loopAt
      .product .power id false .transfer (some .guard)
  | .cleanup => MachineDrain.drain .fuel .cleanup none

end DFVSGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudPadding
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.PreprocessingPaddingOffsets

open PreprocessingRegularTables
open scoped BigOperators

theorem paddingOrder_val {n : Nat} (padding : Fin n → Nat)
    (v : Fin n) (j : Fin (padding v)) :
    (PreprocessingRegularTables.paddingOrder padding ⟨v, j⟩).val =
      offset padding v.val + j.val := by
  change (paddingList padding).idxOf ⟨v, j⟩ = _
  have h := sigma_idxOf padding (List.finRange n) v (List.mem_finRange v) j
  simpa only [List.idxOf_finRange, paddingList, offset] using h

theorem vertexOrder_dummy_val (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (v : Fin t.vertices) (j : Fin (padding v)) :
    (vertexOrder t padding (Sum.inr ⟨v, j⟩)).val =
      t.darts + offset padding v.val + j.val := by
  rw [vertexOrder_dummy, paddingOrder_val]
  omega

end DFVSGames.Foundations.PCP.PreprocessingPaddingOffsets

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_Overlay
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace DFVSGames.Foundations.PCP.ConstraintGraph

variable {V E A : Type*}

section Minimum

variable [Fintype V] [Fintype E] [Fintype A] [Nonempty A]

def rejectionCounts (G : ConstraintGraph V E A) : Finset Nat := by
  classical
  exact Finset.univ.image G.rejectionCount

theorem rejectionCounts_nonempty (G : ConstraintGraph V E A) :
    G.rejectionCounts.Nonempty := by
  classical
  exact Finset.univ_nonempty.image G.rejectionCount

def minimumRejections (G : ConstraintGraph V E A) : Nat :=
  G.rejectionCounts.min' G.rejectionCounts_nonempty

def gap (G : ConstraintGraph V E A) : ℝ :=
  (G.minimumRejections : ℝ) / Fintype.card E

end Minimum

variable {W D B : Type*}

def reindex (G : ConstraintGraph V E A) (vertices : V ≃ W) (darts : E ≃ D)
    (labels : A ≃ B) : ConstraintGraph W D B where
  reverse := darts.symm.trans (G.reverse.trans darts)
  reverse_involutive := by
    intro d
    change darts (G.reverse (darts.symm (darts (G.reverse (darts.symm d))))) = d
    rw [darts.symm_apply_apply, G.reverse_involutive, darts.apply_symm_apply]
  tail := fun d => vertices (G.tail (darts.symm d))
  accepts := fun d a b => G.accepts (darts.symm d) (labels.symm a) (labels.symm b)
  reverse_accepts := by
    intro d a b
    simpa only [Equiv.trans_apply, darts.symm_apply_apply] using
      G.reverse_accepts (darts.symm d) (labels.symm a) (labels.symm b)

end DFVSGames.Foundations.PCP.ConstraintGraph

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PoweringReach
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.GenericGraphTables

open DFVSGames.Foundations.Complexity

variable {q : Nat}

def tableWords (table : (Table q)) : List Nat :=
  [table.vertices, table.darts] ++ (rowList table).flatMap rowWords

def tableBits (table : (Table q)) : List Bool := encodeWords (tableWords table)

end DFVSGames.Foundations.PCP.GenericGraphTables

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_VerifierCNF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.VerifierToCNF

open Target

def splitLong {n : Nat} : List (Literal n) → List (Fin n) → List (Clause n)
  | [a, b, c], [] => [#v[a, b, c]]
  | a :: b :: rest, y :: ys =>
      #v[a, b, ⟨y, true⟩] :: splitLong (⟨y, false⟩ :: rest) ys
  | _, _ => []

def tautology {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    Clause (outputVariables V) :=
  let v := oldIndex V (V.query e ⟨0, by omega⟩)
  #v[⟨v, true⟩, ⟨v, false⟩, ⟨v, true⟩]

def block {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events)
    (p : PatternIndex q) : List (Clause (outputVariables V)) :=
  if V.accepts e (patternAt q p) then List.replicate (q - 2) (tautology V hq e)
  else splitLong (forbiddenClause V e p) (auxiliaryNames V e p)

def eventBlock {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (e : Fin V.events) :
    List (Clause (outputVariables V)) :=
  (List.finRange (patterns q).length).flatMap (block V hq e)

def convert {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) : Formula where
  «variables» := outputVariables V
  clauses := (List.finRange V.events).flatMap (eventBlock V hq)

theorem splitLong_values {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (A : Fin n → Bool) :
    (splitLong ls ys).map (fun c => c.eval A) =
      (chainView (ls.map (fun l => l.eval A)) (ys.map A)).map tripleValue := by
  induction ys generalizing ls with
  | nil =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | [_, _] => rfl
    | [a, b, c] => rfl
    | _ :: _ :: _ :: _ :: _ => rfl
  | cons y ys ih =>
    match ls with
    | [] => rfl
    | [_] => rfl
    | a :: b :: rest =>
      have h := ih (⟨y, false⟩ :: rest)
      simp only [splitLong, List.map_cons, chainView]
      apply congrArg₂ List.cons
      · rfl
      · simpa only [List.map_cons, Literal.eval, Bool.false_eq_true, ↓reduceIte] using h

theorem splitLong_length {n : Nat} (ls : List (Literal n)) (ys : List (Fin n))
    (size : ls.length = ys.length + 3) : (splitLong ls ys).length = ys.length + 1 := by
  have values := congrArg List.length (splitLong_values ls ys (fun _ => false))
  simp only [List.length_map] at values
  rw [values]
  have h := chainView_length (ls.map (fun l => l.eval (fun _ => false)))
    (ys.map (fun _ => false)) (by simpa only [List.length_map] using size)
  simpa only [List.length_map] using h

theorem block_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) (p : PatternIndex q) : (block V hq e p).length = q - 2 := by
  by_cases accepted : V.accepts e (patternAt q p) = true
  · simp [block, accepted]
  · simp only [block, accepted, Bool.false_eq_true, ↓reduceIte]
    have size : (forbiddenClause V e p).length = (auxiliaryNames V e p).length + 3 := by
      simp only [forbiddenClause, auxiliaryNames, List.length_ofFn]
      omega
    have h := splitLong_length (forbiddenClause V e p) (auxiliaryNames V e p) size
    have auxLength : (auxiliaryNames V e p).length = q - 3 := by simp [auxiliaryNames]
    rw [auxLength] at h
    omega

theorem eventBlock_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (e : Fin V.events) : (eventBlock V hq e).length = 2 ^ q * (q - 2) := by
  rw [eventBlock, length_flatMap_constant _ _ (q - 2) (fun p _ => block_length V hq e p)]
  simp only [List.length_finRange, patterns_length]

theorem convert_clause_count {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) :
    (convert V hq).clauses.length = V.events * (2 ^ q * (q - 2)) := by
  change ((List.finRange V.events).flatMap (eventBlock V hq)).length = _
  rw [length_flatMap_constant _ _ _ (fun e _ => eventBlock_length V hq e)]
  rw [List.length_finRange]

theorem twelve_query_clause_count (V : FiniteVerifier 12) :
    (convert V (by decide)).clauses.length = V.events * 40960 := by
  simpa only [twelve_query_factor] using convert_clause_count V (by decide)

end DFVSGames.Foundations.PCP.VerifierToCNF

namespace DFVSGames.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

abbrev verifier (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    VerifierToCNF.FiniteVerifier 12 where
  «variables» := n * 6
  events := m
  query := fun e i => Fin.addCases (motive := fun _ : Fin (6 + 6) => Fin (n * 6))
    (fun j : Fin 6 => bitIndex vertices (G.tail (edges.symm e)) j)
    (fun j : Fin 6 => bitIndex vertices (G.head (edges.symm e)) j) i
  accepts := fun e bits => G.accepts (edges.symm e)
    (fun j => bits (Fin.castAdd 6 j)) (fun j => bits (Fin.natAdd 6 j))

def cnf (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n) (edges : E ≃ Fin m) : Formula :=
  VerifierToCNF.convert (verifier G vertices edges) (by decide)

theorem cnf_clause_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).clauses.length = m * 40960 :=
  VerifierToCNF.twelve_query_clause_count (verifier G vertices edges)

theorem cnf_variable_count (G : ConstraintGraph V E Label) (vertices : V ≃ Fin n)
    (edges : E ≃ Fin m) : (cnf G vertices edges).«variables» = n * 6 + m * 36864 := by
  change n * 6 + m * (VerifierToCNF.patterns 12).length * (12 - 3) = _
  rw [VerifierToCNF.patterns_length, Nat.mul_assoc, twelve_query_auxiliary_factor]

end DFVSGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_InitialGraph
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.InitialGraph

open Target

abbrev Vertex (F : Formula) := (Fin F.«variables» ⊕ Fin F.clauses.length) ⊕ Unit
abbrev Dart (F : Formula) := (RandomEvent F × Bool) ⊕ Unit

instance slotFintype : Fintype Slot where
  elems := {Slot.first, Slot.second, Slot.third}
  complete := by intro s; cases s <;> simp

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

def variableVertex (F : Formula) (v : Fin F.«variables») : Vertex F := .inl (.inl v)
def clauseVertex (F : Formula) (i : Fin F.clauses.length) : Vertex F := .inl (.inr i)
def dummyVertex (F : Formula) : Vertex F := .inr ()

def reverse (F : Formula) : Dart F → Dart F
  | .inl (event, orientation) => .inl (event, !orientation)
  | .inr _ => .inr ()

theorem reverse_involutive (F : Formula) : Function.Involutive (reverse F) := by
  intro d
  cases d with
  | inl pair => rcases pair with ⟨e, b⟩; cases b <;> rfl
  | inr u => cases u; rfl

def reverseEquiv (F : Formula) : Dart F ≃ Dart F where
  toFun := reverse F
  invFun := reverse F
  left_inv := reverse_involutive F
  right_inv := reverse_involutive F

def tail (F : Formula) : Dart F → Vertex F
  | .inl (event, false) => clauseVertex F event.1
  | .inl (event, true) => variableVertex F (nameAt (clauseAt F event.1) event.2)
  | .inr _ => dummyVertex F

def toClauseAnswer (label : Label) : ClauseAnswer := ⟨label.1, label.2.1, label.2.2⟩
def fromClauseAnswer (answer : ClauseAnswer) : Label := (answer.first, answer.second, answer.third)

@[simp] theorem to_fromClauseAnswer (answer : ClauseAnswer) :
    toClauseAnswer (fromClauseAnswer answer) = answer := by
  cases answer; rfl

def incidenceAccept (F : Formula) (event : RandomEvent F)
    (clauseLabel variableAnswer : Label) : Bool :=
  variableValid variableAnswer &&
    (localSatisfies (clauseAt F event.1) (toClauseAnswer clauseLabel) &&
      decide (answerAt (toClauseAnswer clauseLabel) event.2 = variableAnswer.1))

def predicate (F : Formula) : Dart F → Label → Label → Bool
  | .inl (event, false), a, b => incidenceAccept F event a b
  | .inl (event, true), a, b => incidenceAccept F event b a
  | .inr _, _, _ => true

def raw (F : Formula) : ConstraintGraph (Vertex F) (Dart F) Label where
  reverse := reverseEquiv F
  reverse_involutive := reverse_involutive F
  tail := tail F
  accepts := predicate F
  reverse_accepts := by
    intro d a b
    cases d with
    | inl pair => rcases pair with ⟨event, orientation⟩; cases orientation <;> rfl
    | inr u => rfl

@[simp] theorem card_vertex (F : Formula) :
    Fintype.card (Vertex F) = F.«variables» + F.clauses.length + 1 := by
  simp [Vertex, Fintype.card_sum]

@[simp] theorem card_dart (F : Formula) :
    Fintype.card (Dart F) = 6 * F.clauses.length + 1 := by
  simp [Dart, RandomEvent, Fintype.card_sum, Fintype.card_prod]
  omega

end DFVSGames.Foundations.PCP.InitialGraph

namespace DFVSGames.Foundations.PCP.AlphabetRetraction

variable {V E A B : Type*}

def pullback (G : ConstraintGraph V E A) (decode : B → A) : ConstraintGraph V E B where
  reverse := G.reverse
  reverse_involutive := G.reverse_involutive
  tail := G.tail
  accepts := fun e b c => G.accepts e (decode b) (decode c)
  reverse_accepts := fun e b c => G.reverse_accepts e (decode b) (decode c)

@[simp] theorem edgeSatisfied_pullback (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) (e : E) :
    (pullback G decode).edgeSatisfied labeling e =
      G.edgeSatisfied (decode ∘ labeling) e := rfl

@[simp] theorem rejectionCount_pullback [Fintype E] (G : ConstraintGraph V E A)
    (decode : B → A) (labeling : V → B) :
    (pullback G decode).rejectionCount labeling =
      G.rejectionCount (decode ∘ labeling) := rfl

abbrev Label64 := QueryIncidence.Label 6

def decode64 (label : Label64) : InitialGraph.Label := (label 0, label 1, label 2)

def encode64 (label : InitialGraph.Label) : Label64 :=
  fun i => if i = 0 then label.1 else if i = 1 then label.2.1 else label.2.2

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, c⟩
  rfl

end DFVSGames.Foundations.PCP.AlphabetRetraction

namespace DFVSGames.Foundations.PCP.RawInitialTables

open Target GraphTables

def slotOrder : Slot ≃ Fin 3 where
  toFun
    | .first => 0
    | .second => 1
    | .third => 2
  invFun i := if i = 0 then .first else if i = 1 then .second else .third
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

def labelOrder : AlphabetRetraction.Label64 ≃ GraphTables.Label := binaryOrder 6

def vertexOrder (F : Formula) :
    InitialGraph.Vertex F ≃ Fin (F.«variables» + F.clauses.length + 1) :=
  ((finSumFinEquiv.sumCongr unitOrder).trans finSumFinEquiv)

def eventOrder (F : Formula) : RandomEvent F ≃ Fin (F.clauses.length * 3) :=
  ((Equiv.refl (Fin F.clauses.length)).prodCongr slotOrder).trans finProdFinEquiv

def dartOrder (F : Formula) : InitialGraph.Dart F ≃ Fin (6 * F.clauses.length + 1) :=
  (((((eventOrder F).prodCongr finTwoEquiv.symm).trans finProdFinEquiv).sumCongr
    unitOrder).trans finSumFinEquiv).trans (finCongr (by omega))

def raw64 (F : Formula) : ConstraintGraph (InitialGraph.Vertex F)
    (InitialGraph.Dart F) AlphabetRetraction.Label64 :=
  AlphabetRetraction.pullback (InitialGraph.raw F) AlphabetRetraction.decode64

def table (F : Formula) : GraphTables.Table :=
  GraphTables.ofEnumeratedGraph (raw64 F) (vertexOrder F) (dartOrder F) labelOrder

@[simp] theorem table_vertices (F : Formula) :
    (table F).vertices = F.«variables» + F.clauses.length + 1 := rfl

@[simp] theorem table_darts (F : Formula) : (table F).darts = 6 * F.clauses.length + 1 := rfl

end DFVSGames.Foundations.PCP.RawInitialTables

noncomputable section

namespace DFVSGames.Foundations.PCP.FiniteGraph

structure Bundle (A : Type) where
  Vertex : Type
  Dart : Type
  vertexFintype : Fintype Vertex
  dartFintype : Fintype Dart
  vertexDecidableEq : DecidableEq Vertex
  dartDecidableEq : DecidableEq Dart
  dartNonempty : Nonempty Dart
  graph : ConstraintGraph Vertex Dart A

namespace Bundle

variable {A : Type}

instance instFintypeVertex (G : Bundle A) : Fintype G.Vertex := G.vertexFintype
instance instFintypeDart (G : Bundle A) : Fintype G.Dart := G.dartFintype

def ofGraph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) : Bundle A where
  Vertex := V
  Dart := E
  vertexFintype := inferInstance
  dartFintype := inferInstance
  vertexDecidableEq := inferInstance
  dartDecidableEq := inferInstance
  dartNonempty := inferInstance
  graph := G

def size (G : Bundle A) : Nat := Fintype.card G.Vertex + Fintype.card G.Dart

def rejectionCount (G : Bundle A) (labeling : G.Vertex → A) : Nat :=
  G.graph.rejectionCount labeling

@[simp] theorem ofGraph_graph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).graph = G := rfl

@[simp] theorem ofGraph_size {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).size = Fintype.card V + Fintype.card E := rfl

@[simp] theorem ofGraph_rejectionCount {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) (labeling : V → A) :
    (ofGraph G).rejectionCount labeling = G.rejectionCount labeling := rfl

variable [Fintype A] [Nonempty A]

def minimumRejections (G : Bundle A) : Nat := G.graph.minimumRejections

def gap (G : Bundle A) : ℝ := G.graph.gap

@[simp] theorem ofGraph_minimumRejections {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).minimumRejections = G.minimumRejections := rfl

@[simp] theorem ofGraph_gap {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).gap = G.gap := rfl

end Bundle

end DFVSGames.Foundations.PCP.FiniteGraph

end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

abbrev labelEquiv : Label ≃ Fin 64 := AlphabetTable.Enumeration.labelEquiv

def labelIndex (label : Label) : Fin 64 := labelEquiv label

def relationAddress (bits : VerifierToCNF.Pattern 12) : Fin 4096 :=
  GraphTables.relationIndex (labelIndex (leftHalf bits), labelIndex (rightHalf bits))

def patternRelationIndex (p : VerifierToCNF.PatternIndex 12) : Fin 4096 :=
  relationAddress (VerifierToCNF.patternAt 12 p)

@[simp] theorem patternRelationIndex_eq (p : VerifierToCNF.PatternIndex 12) :
    patternRelationIndex p = relationAddress (VerifierToCNF.patternAt 12 p) := rfl

def tableGraph (table : GraphTables.Table) :
    ConstraintGraph (Fin table.vertices) (Fin table.darts) Label :=
  (GraphTables.semantics table).reindex (Equiv.refl _) (Equiv.refl _) labelEquiv.symm

@[simp] theorem tableGraph_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).tail e = table.rows[e].tail := rfl

@[simp] theorem tableGraph_reverse (table : GraphTables.Table) (e : Fin table.darts) :
    (tableGraph table).reverse e = table.rows[e].reverseIndex := rfl

@[simp] theorem tableGraph_accepts (table : GraphTables.Table) (e : Fin table.darts)
    (a b : Label) :
    (tableGraph table).accepts e a b =
      GraphTables.relationAt table.rows[e].relation (labelIndex a) (labelIndex b) := rfl

end DFVSGames.Foundations.Complexity.FinalCNFPattern

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_PoweringFinalConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).«variables» = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

@[simp] theorem clause_count (table : GraphTables.Table) :
    (output table).clauses.length = table.darts * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ (Equiv.refl _) (Equiv.refl _)

end DFVSGames.Foundations.PCP.FinalTableFormula

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_Lookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open DFVSGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

def headIndex {q : Nat} (table : Table q) (e : Fin table.darts) : Fin table.darts :=
  table.rows[e].reverseIndex

def headValue {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  table.rows[headIndex table e].tail.val

theorem headValue_eq_semantics {q : Nat} (table : Table q) (e : Fin table.darts) :
    headValue table e = ((semantics table).head e).val := rfl

def headLookupTapes {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) : K → List Bool :=
  MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
    (encodeWord 0 ++ base (tape 3))
    (encodeWord table.rows[headIndex table e].reverseIndex.val ++
      (encodeWords (relationWords table.rows[headIndex table e].relation) ++
        (rowsBits ((rowList table).drop ((headIndex table e).val + 1)) ++ base (tape 2))))
    (encodeWord (headValue table e))

end DFVSGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_EmitRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.AlphabetTable.LoopState

open DFVSGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

@[simp] theorem cursorBits_full (input : GenericGraphTables.Table q) :
    cursorBits input input.darts = [] := by
  have finished := List.drop_length (l := GenericGraphTables.rowList input)
  rw [GenericGraphTables.rowList_length] at finished
  unfold cursorBits cursorWords
  rw [finished]
  rfl

end DFVSGames.Foundations.PCP.AlphabetTable.LoopState

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineStateEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineUnaryEqualityBit

open Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

def instruction (tape : Fin 6 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .seedLeft => MachineUnaryAffineAt.seed (tape 2) 0 (labels .scanLeft)
  | .scanLeft => MachineUnaryAffineAt.scan (tape 0) (tape 4) (tape 2) 1
      (labels .scanLeft) (labels .restoreLeft)
  | .restoreLeft => Reduction.MachineTransfer.loopAt (tape 4) (tape 0) id false
      (labels .restoreLeft) (some (labels .seedRight))
  | .seedRight => MachineUnaryAffineAt.seed (tape 3) 0 (labels .scanRight)
  | .scanRight => MachineUnaryAffineAt.scan (tape 1) (tape 4) (tape 3) 1
      (labels .scanRight) (labels .restoreRight)
  | .restoreRight => Reduction.MachineTransfer.loopAt (tape 4) (tape 1) id false
      (labels .restoreRight) (some (labels .compare))
  | .compare => MachineStateEquiv.statement (compareStateEquiv A)
      (MachineCompare.loop (tape 2) (tape 3) (labels .compare)
        (some (labels .equal)) (some (labels .different)))
  | .equal => emit (tape 5) true exit
  | .different => emit (tape 5) false exit

end DFVSGames.Foundations.Complexity.MachineUnaryEqualityBit

namespace DFVSGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open DFVSGames.Foundations.PCP

abbrev Field (S : Nat) := (GraphTables.Label × GraphTables.Label) ⊕ (Fin S ⊕ Fin S)

def fieldEquiv (S : Nat) : Field S ≃ Fin (4096 + (S + S)) :=
  (Equiv.sumCongr GraphTables.relationIndex
    (finSumFinEquiv : (Fin S ⊕ Fin S) ≃ Fin (S + S))).trans finSumFinEquiv

def inputEquiv (t S : Nat) : (Fin t × Field S) ≃ Fin (inputSize t S) :=
  (Equiv.prodCongr (Equiv.refl (Fin t)) (fieldEquiv S)).trans finProdFinEquiv

def packData {t S : Nat} (data : Fin t → Field S → Bool) : Buffer (inputSize t S) :=
  fun i => data ((inputEquiv t S).symm i).1 ((inputEquiv t S).symm i).2

@[simp] theorem packData_inputEquiv {t S : Nat}
    (data : Fin t → Field S → Bool) (k : Fin t) (f : Field S) :
    packData data (inputEquiv t S (k, f)) = data k f := by
  simp [packData]

def basePredicate {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (a b : GraphTables.Label) : Bool :=
  bits (inputEquiv t S (k, .inl (a, b)))

def leftMatches {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (i : Fin S) : Bool :=
  bits (inputEquiv t S (k, .inr (.inl i)))

def rightMatches {t S : Nat} (bits : Buffer (inputSize t S))
    (k : Fin t) (i : Fin S) : Bool :=
  bits (inputEquiv t S (k, .inr (.inr i)))

def edgeAccept {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : Fin q) : Bool :=
  match firstMatch (leftMatches bits k), firstMatch (rightMatches bits k) with
  | some i, some j => basePredicate bits k (labelAt a i) (labelAt b j)
  | _, _ => false

def rowAccept {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) : Bool :=
  (List.ofFn id).all (fun k : Fin t => edgeAccept labelAt bits k a b)

def rowBlock {t S q : Nat} (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) : Buffer (q * q) :=
  fun i => rowAccept labelAt bits
    ((GenericGraphTables.relationIndex q).symm i).1
    ((GenericGraphTables.relationIndex q).symm i).2

@[simp] theorem rowBlock_at {t S q : Nat}
    (labelAt : Fin q → Fin S → GraphTables.Label)
    (bits : Buffer (inputSize t S)) (a b : Fin q) :
    rowBlock labelAt bits (GenericGraphTables.relationIndex q (a, b)) =
      rowAccept labelAt bits a b := by
  simp [rowBlock]

section Chains

variable {K Λ σ : Type} {N : Nat}

def readEncodedSlots (src : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop src (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (.branch (fun state => state.2 i)
          (.pop src (fun state _ => state) (readEncodedSlots src slots next))
          (readEncodedSlots src slots next))

variable [DecidableEq K]

def writeEncodedSlots {M : Nat} (dst : K) (emit : σ → Buffer M) : List (Fin M) →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], next => next
  | i :: slots, next => .push dst (fun _ => false)
      (.branch (fun state => emit state i)
        (.push dst (fun _ => true) (writeEncodedSlots dst emit slots next))
        (writeEncodedSlots dst emit slots next))

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

def encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readEncodedSlots src (List.ofFn id)
    (writeEncodedSlots dst (fun state => F state.2) (List.ofFn id).reverse
      (.load (fun state => (state.1, emptyBuffer N)) next))

def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  encodedBlockStmt src dst F (finishAt exit)

end Block

end DFVSGames.Foundations.Complexity.PoweringMachineRow

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePreservingLookupClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def statement (tape : Fin 5 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .run label => MachineSubroutine.statement (fun label => labels (.run label))
      (some (labels .cleanup)) (MachinePreservingLookup.program tape label)
  | .cleanup => MachineDrain.drain (tape 2) (labels .cleanup) exit

end DFVSGames.Foundations.Complexity.MachinePreservingLookupClean


end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineCloudSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace DFVSGames.Foundations.PCP.PreprocessingInternalRows

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

def localStep (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    Fin (cloudSize t v + padding v) × Fin q :=
  ExpanderTables.lookup (tables v) (paddedCloudRank t padding v x, p)

def rowIndex (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    Fin (vertexCount t padding * (q + 1)) :=
  PortTables.rowIndex (vertexCount t padding) (q + 1)
    (vertexOrder t padding x.val, portOrder q (.inl p))

def row (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[rowIndex t padding v x p]

def equalityRelation : GraphTables.RelationTable :=
  GraphTables.relationOf (fun a b => decide (a = b))

@[simp] theorem equalityRelation_apply (a b : GraphTables.Label) :
    GraphTables.relationAt equalityRelation a b = decide (a = b) :=
  GraphTables.relationAt_relationOf _ a b

theorem relation_ext_inline_PreprocessingInternalRows {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using
    h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

theorem relations_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (ofCloudTables t padding tables).relations[rowIndex t padding v x p] = equalityRelation := by
  apply relation_ext_inline_PreprocessingInternalRows
  intro a b
  rw [equalityRelation_apply]
  exact accepts_internal t padding tables x.val p a b

@[simp] theorem row_tail (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).tail.val = (vertexOrder t padding x.val).val := by
  simp only [row, rowIndex, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

@[simp] theorem row_relation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).relation = equalityRelation := by
  simpa only [row, PortTables.flatRows, Vector.getElem_ofFn, Fin.getElem_fin] using
    relations_internal t padding tables v x p

@[simp] theorem localStep_original (v : Fin t.vertices) (x : Cloud (GraphTables.semantics t) v)
    (p : Fin q) :
    localStep t padding tables v (paddedOld t padding v x) p =
      ExpanderTables.lookup (tables v) (Fin.castAdd (padding v) (cloudRank t v x), p) := rfl

@[simp] theorem localStep_dummy (v : Fin t.vertices) (j : Fin (padding v)) (p : Fin q) :
    localStep t padding tables v (paddedNew t padding v j) p =
      ExpanderTables.lookup (tables v) (Fin.natAdd (cloudSize t v) j, p) := rfl

@[simp] theorem row_tail_original (v : Fin t.vertices) (x : Cloud (GraphTables.semantics t) v)
    (p : Fin q) :
    (row t padding tables v (paddedOld t padding v x) p).tail.val = x.val.val := by
  rw [row_tail]
  rfl

@[simp] theorem row_tail_dummy (v : Fin t.vertices) (j : Fin (padding v)) (p : Fin q) :
    (row t padding tables v (paddedNew t padding v j) p).tail.val =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val := by
  rw [row_tail]
  exact PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v j

end DFVSGames.Foundations.PCP.PreprocessingInternalRows

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

def outputOffset {d : Nat} (s : Control d) : Fin (rowFactor d) :=
  rowIndex (cloudSize d) (degree d) (s.lastH.1,outputPort s)

def outputAddress {d : Nat} (vertex : Nat) (s : Control d) : Nat :=
  rowFactor d * vertex + (outputOffset s).val

theorem rowIndex_lookup {v q : Nat} (G : Table v q) (x : Fin v × Fin q) :
    rowIndex v q (lookup G x) = reverseIndex G (rowIndex v q x) := by
  simp only [lookup, Equiv.apply_symm_apply]

def outputPair {v d : Nat} (vertex : Fin v) (s : Control d) :
    Fin (v * cloudSize d) × Fin (degree d) :=
  (rowIndex v (cloudSize d) (vertex,s.lastH.1),outputPort s)

theorem outputAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    outputAddress vertex.val s =
      (rowIndex (v * cloudSize d) (degree d) (outputPair vertex s)).val := by
  simp only [outputAddress, outputOffset, outputPair, rowIndex_val, rowFactor]
  ring

def evaluateRow {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    Fin v × Control d :=
  let s₀ := start H cloud port
  let g₁ := lookup G (vertex,firstOffset s₀)
  let s₁ := receiveFirst s₀ g₁.2
  let g₂ := lookup G (g₁.1,secondOffset s₁)
  (g₂.1, receiveSecond H s₁ g₂.2)

theorem evaluateRow_eq_lookup_step {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputPair (evaluateRow G H vertex cloud port).1 (evaluateRow G H vertex cloud port).2 =
      lookup (step G H) (rowIndex v (cloudSize d) (vertex,cloud),port) := by
  rw [lookup_step]
  simp only [evaluateRow, start, receiveFirst, receiveSecond, firstOffset, secondOffset,
    squarePorts, outputPair, outputPort, stepLookup, Equiv.symm_apply_apply]

theorem outputAddress_eq_step_row {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (rowIndex (v * cloudSize d) (degree d)
        (lookup (step G H) (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_rowIndex, evaluateRow_eq_lookup_step]

theorem outputAddress_eq_step_reverseIndex {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (reverseIndex (step G H) (rowIndex (v * cloudSize d) (degree d)
        (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_step_row, rowIndex_lookup]

end DFVSGames.Foundations.PCP.ExpanderRowControl
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_ExpanderTableWords
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open DFVSGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

theorem rotationWords_getElem (table : Table v d) (i : ℕ) (hi : i < v * d) :
    (rotationWords table)[i]'(by simpa only [rotationWords_length] using hi) =
      (reverseIndex table ⟨i, hi⟩).val := by
  simp only [rotationWords, List.getElem_map, Vector.getElem_toList,
    reverseIndex, Fin.getElem_fin]

end DFVSGames.Foundations.PCP.ExpanderTableWords
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

def firstFinish {ρ : Type} {d : Nat} (s : Ambient ρ d × Unit)
    (r : Fin (degree d)) : Ambient ρ d × Unit :=
  ((s.1.1, receiveFirst s.1.2 r), ())

def secondFinish {ρ : Type} {d : Nat} (H : Table (cloudSize d) d)
    (s : Ambient ρ d × Unit) (r : Fin (degree d)) : Ambient ρ d × Unit :=
  ((s.1.1, receiveSecond H s.1.2 r), ())

def affinePlan {σ : Type} {bound : Nat} (coefficient : Nat) (offset : σ → Fin bound) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 σ bound :=
  PCP.AlphabetTable.Emitter.listCommands
    (PCP.AlphabetTable.Emitter.affineCommands [(0, coefficient)] offset)

def firstPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (degree d) :=
  affinePlan (degree d) (fun s => firstOffset s.1.2)

def secondPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (degree d) :=
  affinePlan (degree d) (fun s => secondOffset s.1.2)

def outputPlan (ρ : Type) (d : Nat) :
    Fin 3 → PCP.AlphabetTable.Emitter.Command 1 (Ambient ρ d × Fin (degree d)) (rowFactor d) :=
  affinePlan (rowFactor d) (fun s => outputOffset s.1.2)

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

def statement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d)
  | .initialize_ =>
    .push (ports .quotientFirst) (fun _ => false)
      (.push (ports .quotientSecond) (fun _ => false)
        (.push (ports .remainderFirst) (fun _ => false)
          (.push (ports .remainderSecond) (fun _ => false)
            (.load (fun s => (s.1, none))
              (.goto fun _ => labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry)))))))
  | .firstEmit l =>
    PCP.AlphabetTable.Emitter.statement (firstPlan ρ d) (fun _ => ports .inputVertex)
      (ports .emitScratch) (ports .queryReverse) (fun k => labels (.firstEmit k))
      (some (labels .firstReverse)) l
  | .firstReverse =>
    Reduction.MachineTransfer.loopAt (ports .queryReverse) (ports .queryIndex)
      id false (labels .firstReverse)
      (some (labels (.firstLookup (.run .copyFirst))))
  | .firstLookup l =>
    MachinePreservingLookupClean.statement (ports ∘ lookupTape)
      (fun k => labels (.firstLookup k)) (some (labels .firstScan)) l
  | .firstScan =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r)))
  | .firstResidue r =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
        (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r)
  | .clearQuery =>
    .pop (ports .queryIndex) (fun s _ => s)
      (.pop (ports .lookupOutput) (fun s _ => s)
        (.goto fun _ => labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
  | .secondEmit l =>
    PCP.AlphabetTable.Emitter.statement (secondPlan ρ d) (fun _ => ports .quotientFirst)
      (ports .emitScratch) (ports .queryReverse) (fun k => labels (.secondEmit k))
      (some (labels .secondReverse)) l
  | .secondReverse =>
    Reduction.MachineTransfer.loopAt (ports .queryReverse) (ports .queryIndex)
      id false (labels .secondReverse)
      (some (labels (.secondLookup (.run .copyFirst))))
  | .secondLookup l =>
    MachinePreservingLookupClean.statement (ports ∘ lookupTape)
      (fun k => labels (.secondLookup k)) (some (labels .secondScan)) l
  | .secondScan =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r)))
  | .secondResidue r =>
    MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
        (ports .remainderSecond)
        (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
        (secondFinish H) r)
  | .outputEmit l =>
    PCP.AlphabetTable.Emitter.statement (outputPlan ρ d) (fun _ => ports .quotientSecond)
      (ports .emitScratch) (ports .output) (fun k => labels (.outputEmit k))
      (some (labels (.cleanup 0))) l
  | .cleanup i =>
    MachineDrain.drain (ports (dirtyTape i)) (labels (.cleanup i))
      (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩) else labels .done))
  | .done => Reduction.MachineTransfer.exitAt (ports .output) exit

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    Label d → TM2.Stmt (fun _ : Tape => Bool) (Label d) (State ρ d) :=
  statement positive H id id none

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRowDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

def initialState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) : State ρ d :=
  boundaryState positive H ambient (zeroPosition positive)

def resetState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  initialState positive H (caller s)

def clearRegister {ρ : Type} {d : Nat} (s : State ρ d) : State ρ d :=
  ((s.1.1, none), s.2)

def vertexGuardCore {ρ : Type} {d : Nat} :
    TM2.Stmt Alphabet (Label d) ((RowStatePrefix ρ d × Position d) × Option Bool) :=
  .peek (.inr .vertexCount) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.pop (.inr .vertexCount) (fun s _ => (s.1, none))
        (.goto fun _ => .inr .prepareRow))
      (.load (fun s => (s.1, none)) (.goto fun _ => .inr .reverseOutput)))

variable {ρ : Type} [Fintype ρ]

def outerStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    OuterLabel → TM2.Stmt Alphabet (Label d) (State ρ d)
  | .initialize_ =>
    .push (.inl .inputVertex) (fun _ => false)
      (.load (resetState positive H) (.goto fun _ => .inr .vertexGuard))
  | .vertexGuard => MachineControl.statement id (guardStates ρ d) vertexGuardCore
  | .prepareRow =>
    .load (prepareState positive H) (.goto fun _ => .inl .initialize_)
  | .afterRow =>
    .branch (fun s => decide (s.2.val + 1 < rowFactor d))
      (.load (advancePositionState positive) (.goto fun _ => .inr .prepareRow))
      (.push (.inl .inputVertex) (fun _ => true)
        (.load (resetPositionState positive) (.goto fun _ => .inr .vertexGuard)))
  | .reverseOutput =>
    MachineControl.statement id (guardStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := Alphabet) (Λ := Label d)
        (σ := RowStatePrefix ρ d × Position d) (.inl .output) (.inr .result) id false
        (.inr .reverseOutput) (some (.inr .done)))
  | .done => .halt

def rowReturn (d : Nat) : Option (Label d) := some (.inr .afterRow)

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    Label d → TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineEmbedding.program (rowReturn d) (MachineExpanderRow.program positive H)
    (outerStatement positive H)

@[simp] theorem program_row {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (label : MachineExpanderRow.Label d) :
    program (ρ := ρ) positive H (.inl label) =
      MachineEmbedding.statement (rowReturn d)
        (MachineExpanderRow.program positive H label) := rfl

@[simp] theorem program_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (label : OuterLabel) :
    program (ρ := ρ) positive H (.inr label) = outerStatement positive H label := rfl

def rowExecution {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (position : Position d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg (fun _ : MachineExpanderRow.Tape => Bool)
      (MachineExpanderRow.Label d) (MachineExpanderRow.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderRow.program positive H)) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      (MachineEmbedding.configuration (rowReturn d) position extra a)
      (some (MachineEmbedding.configuration (rowReturn d) position extra b)) budget :=
  MachineComposition.embeddedExecution (rowReturn d) position extra
    (MachineExpanderRow.program positive H) (outerStatement positive H) execution

@[simp] theorem rowExecution_steps {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (position : Position d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg (fun _ : MachineExpanderRow.Tape => Bool)
      (MachineExpanderRow.Label d) (MachineExpanderRow.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderRow.program positive H)) a (some b) budget) :
    (rowExecution positive H position extra execution).steps = execution.steps := rfl

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

@[simp] theorem tapes_rfl (source : ∀ k, List (Γ k)) : tapes rfl source = source := rfl
@[simp] theorem statement_rfl (source : Stmt Γ Λ σ) : statement rfl source = source := rfl
@[simp] theorem configuration_rfl (source : Cfg Γ Λ σ) : configuration rfl source = source := rfl
@[simp] theorem program_rfl (source : Λ → Stmt Γ Λ σ) : program rfl source = source := rfl

@[simp] theorem program_apply (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (label : Λ) :
    program h source label = statement h (source label) := rfl

@[simp] theorem statement_roundtrip (h : Γ = Δ) (source : Stmt Δ Λ σ) :
    statement h (statement h.symm source) = source := by cases h; rfl

@[simp] theorem statement_symm_roundtrip (h : Γ = Δ) (source : Stmt Γ Λ σ) :
    statement h.symm (statement h source) = source := by cases h; rfl

@[simp] theorem configuration_roundtrip (h : Γ = Δ) (source : Cfg Δ Λ σ) :
    configuration h (configuration h.symm source) = source := by cases h; rfl

@[simp] theorem configuration_symm_roundtrip (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    configuration h.symm (configuration h source) = source := by cases h; rfl

@[simp] theorem program_roundtrip (h : Γ = Δ) (source : Λ → Stmt Δ Λ σ) :
    program h (program h.symm source) = source := by cases h; rfl

@[simp] theorem program_symm_roundtrip (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) :
    program h.symm (program h source) = source := by cases h; rfl

@[simp] theorem tapes_roundtrip (h : Γ = Δ) (source : ∀ k, List (Δ k)) :
    tapes h (tapes h.symm source) = source := by cases h; rfl

@[simp] theorem tapes_symm_roundtrip (h : Γ = Δ) (source : ∀ k, List (Γ k)) :
    tapes h.symm (tapes h source) = source := by cases h; rfl

@[simp] theorem configuration_label (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).l = source.l := by cases h; rfl

@[simp] theorem configuration_state (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).var = source.var := by cases h; rfl

@[simp] theorem configuration_tapes (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).stk = tapes h source.stk := by cases h; rfl

@[simp] theorem configuration_mk (h : Γ = Δ) (label : Option Λ) (state : σ)
    (source : ∀ k, List (Γ k)) :
    configuration h ⟨label, state, source⟩ = ⟨label, state, tapes h source⟩ := by cases h; rfl

@[simp] theorem map_configuration_rfl (source : Option (Cfg Γ Λ σ)) :
    source.map (configuration (rfl : Γ = Γ)) = source := by cases source <;> rfl

variable [DecidableEq K]

def executionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (finish.map (configuration h)) budget where
  steps := execution.steps
  evals_in_steps := by
    cases h
    simpa only [program_rfl, configuration_rfl, map_configuration_rfl]
      using execution.evals_in_steps
  steps_le_m := execution.steps_le_m

@[simp] theorem executionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    (executionInTime h source execution).steps = execution.steps := rfl

def successfulExecutionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (some (configuration h finish)) budget := executionInTime h source execution

@[simp] theorem successfulExecutionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    (successfulExecutionInTime h source execution).steps = execution.steps := rfl

end DFVSGames.Foundations.Complexity.MachineAlphabetTransport

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

abbrev Tape := MachineExpanderTable.Tape ⊕ ExtraTape
abbrev Alphabet : Tape → Type :=
  MachineEmbedding.Alphabet MachineExpanderTable.Alphabet (fun _ : ExtraTape => Bool)
abbrev BoolAlphabet (_ : Tape) := Bool

theorem alphabet_eq : Alphabet = BoolAlphabet := by
  funext tape
  cases tape with
  | inl tape => cases tape <;> rfl
  | inr tape => rfl

abbrev Label (d : Nat) := MachineExpanderTable.Label d ⊕ OuterLabel
abbrev State (ρ : Type) (d : Nat) := MachineExpanderTable.State ρ d × Unit
abbrev RegisterAmbient (ρ : Type) (d : Nat) :=
  (MachineExpanderTable.RowStatePrefix ρ d × MachineExpanderTable.Position d) × Unit

def registerStates (ρ : Type) (d : Nat) :
    (RegisterAmbient ρ d × Option Bool) ≃ State ρ d where
  toFun s := (((s.1.1.1, s.2), s.1.1.2), s.1.2)
  invFun s := (((s.1.1.1, s.1.2), s.2), s.1.1.2)
  left_inv := by rintro ⟨⟨⟨a, p⟩, u⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨⟨a, b⟩, p⟩, u⟩; rfl

@[simp] theorem registerStates_apply (ρ : Type) (d : Nat)
    (s : RegisterAmbient ρ d × Option Bool) :
    registerStates ρ d s = (((s.1.1.1, s.2), s.1.1.2), s.1.2) := rfl

@[simp] theorem registerStates_symm_apply (ρ : Type) (d : Nat) (s : State ρ d) :
    (registerStates ρ d).symm s = (((s.1.1.1, s.1.2), s.2), s.1.1.2) := rfl

def caller {ρ : Type} {d : Nat} (s : State ρ d) : ρ :=
  MachineExpanderTable.caller s.1

def initialState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) : State ρ d :=
  (MachineExpanderTable.initialState positive H ambient, ())

def normalizeState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  initialState positive H (caller s)

def initialEncoding (d : Nat) : List Bool := encodeWords (rotationWords (initial d))

def tableTape : Tape := .inl (.inl .table)
def inputVertexTape : Tape := .inl (.inl .inputVertex)
def vertexCountTape : Tape := .inl (.inr .vertexCount)
def resultTape : Tape := .inl (.inr .result)

def affineSource : AffinePhase → Tape
  | .copyCount => .inr .currentSize
  | .multiplySize => inputVertexTape

def affineDestination : AffinePhase → Tape
  | .copyCount => vertexCountTape
  | .multiplySize => .inr .currentSize

def affineCoefficient (d : Nat) : AffinePhase → Nat
  | .multiplySize => cloudSize d
  | .copyCount => 1

def affineExit (d : Nat) : AffinePhase → Label d
  | .copyCount => .inl (.inr .initialize_)
  | .multiplySize => .inr .drainInputVertex

def affineStatement {ρ : Type} {d : Nat} (phase : AffinePhase) :
    AffineLabel → TM2.Stmt BoolAlphabet (Label d) (State ρ d)
  | .seed =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryAffineAt.seed (Λ := Label d) (σ := RegisterAmbient ρ d)
        (affineDestination phase) 0 (.inr (.affine phase .scan)))
  | .scan =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryAffineAt.scan (Λ := Label d) (σ := RegisterAmbient ρ d)
        (affineSource phase) (.inr .unaryScratch)
        (affineDestination phase) (affineCoefficient d phase)
        (.inr (.affine phase .scan)) (.inr (.affine phase .restore)))
  | .restore =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) (.inr .unaryScratch) (affineSource phase) id false
        (.inr (.affine phase .restore)) (some (affineExit d phase)))

def drainStatement {ρ : Type} {d : Nat} (tape : Tape) (again next : OuterLabel) :
    TM2.Stmt BoolAlphabet (Label d) (State ρ d) :=
  MachineControl.statement id (registerStates ρ d)
    (MachineDrain.drain (Λ := Label d) (σ := RegisterAmbient ρ d)
      tape (.inr again) (some (.inr next)))

variable {ρ : Type} [Fintype ρ]

def boolOuterStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d) :
    OuterLabel → TM2.Stmt BoolAlphabet (Label d) (State ρ d)
  | .initialize_ =>
    Reduction.MachineSubstitution.pushWord tableTape (initialEncoding d).reverse
      (Reduction.MachineSubstitution.pushWord (.inr .currentSize) (encodeWord 1).reverse
        (.load (normalizeState positive H)
          (.goto fun _ => .inr .levelGuard)))
  | .levelGuard =>
    MachineControl.statement id (registerStates ρ d)
      (MachineUnaryCounter.guard (K := Tape) (Λ := Label d) (σ := RegisterAmbient ρ d)
        (.inr .remainingLevel) (.inr (.affine .copyCount .seed)) (.inr .done))
  | .affine phase label => affineStatement phase label
  | .clearOldTable => drainStatement tableTape .clearOldTable .reverseResult
  | .reverseResult =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) resultTape (.inr .tableReverse) id false
        (.inr .reverseResult) (some (.inr .reverseTable)))
  | .reverseTable =>
    MachineControl.statement id (registerStates ρ d)
      (Reduction.MachineTransfer.loopAt (Γ := BoolAlphabet) (Λ := Label d)
        (σ := RegisterAmbient ρ d) (.inr .tableReverse) tableTape id false
        (.inr .reverseTable) (some (.inr .clearCurrentSize)))
  | .clearCurrentSize =>
    drainStatement (.inr .currentSize) .clearCurrentSize (.affine .multiplySize .seed)
  | .drainInputVertex => drainStatement inputVertexTape .drainInputVertex .drainVertexCount
  | .drainVertexCount => drainStatement vertexCountTape .drainVertexCount .levelGuard
  | .done => .load (normalizeState positive H) .halt

def outerStatement {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : OuterLabel) : TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineAlphabetTransport.statement alphabet_eq.symm (boolOuterStatement positive H label)

def tableReturn (d : Nat) : Option (Label d) := some (.inr .clearOldTable)

def program {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (_growth : 1 < cloudSize d) : Label d → TM2.Stmt Alphabet (Label d) (State ρ d) :=
  MachineEmbedding.program (tableReturn d) (MachineExpanderTable.program positive H)
    (outerStatement positive H)

@[simp] theorem program_table {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (label : MachineExpanderTable.Label d) :
    program (ρ := ρ) positive H growth (.inl label) =
      MachineEmbedding.statement (tableReturn d)
        (MachineExpanderTable.program positive H label) := rfl

@[simp] theorem program_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d) (label : OuterLabel) :
    program (ρ := ρ) positive H growth (.inr label) = outerStatement positive H label := rfl

def boolView {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) : Label d → TM2.Stmt BoolAlphabet (Label d) (State ρ d) :=
  MachineAlphabetTransport.program alphabet_eq (program positive H growth)

@[simp] theorem boolView_outer {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d) (label : OuterLabel) :
    boolView (ρ := ρ) positive H growth (.inr label) =
      boolOuterStatement positive H label := by
  change MachineAlphabetTransport.statement alphabet_eq
    (MachineAlphabetTransport.statement alphabet_eq.symm
      (boolOuterStatement positive H label)) = _
  exact MachineAlphabetTransport.statement_roundtrip alphabet_eq _

def tableExecution {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (growth : 1 < cloudSize d) (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg MachineExpanderTable.Alphabet (MachineExpanderTable.Label d)
      (MachineExpanderTable.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderTable.program positive H)) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step (program positive H growth))
      (MachineEmbedding.configuration (tableReturn d) () extra a)
      (some (MachineEmbedding.configuration (tableReturn d) () extra b)) budget :=
  MachineComposition.embeddedExecution (tableReturn d) () extra
    (MachineExpanderTable.program positive H) (outerStatement positive H) execution

@[simp] theorem tableExecution_steps {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (growth : 1 < cloudSize d)
    (extra : ExtraTape → List Bool)
    {a b : TM2.Cfg MachineExpanderTable.Alphabet (MachineExpanderTable.Label d)
      (MachineExpanderTable.State ρ d)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime
      (TM2.step (MachineExpanderTable.program positive H)) a (some b) budget) :
    (tableExecution positive H growth extra execution).steps = execution.steps := rfl

def tableFrame (word : List Bool) : (tape : MachineExpanderTable.Tape) →
    List (MachineExpanderTable.Alphabet tape)
  | .inl .table => word
  | .inl _ => []
  | .inr _ => []

def extraFrame (remaining current : Nat) (levelSuffix : List Bool) : ExtraTape → List Bool
  | .remainingLevel => encodeWord remaining ++ levelSuffix
  | .currentSize => encodeWord current
  | _ => []

def boundaryTapes (remaining current : Nat) (word levelSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (tableFrame word) (extraFrame remaining current levelSuffix)

def initialTapes (level : Nat) (levelSuffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  MachineEmbedding.tapes (tableFrame [])
    (fun tape => match tape with
      | .remainingLevel => encodeWord level ++ levelSuffix
      | _ => [])

def familyTapes {d : Nat} (H : Table (cloudSize d) d) (level : Nat)
    (levelSuffix : List Bool) : (tape : Tape) → List (Alphabet tape) :=
  boundaryTapes 0 (vertexCount (degree d) level)
    (encodeWords (rotationWords (family H level))) levelSuffix

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderFamilyTapes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing

def boolWord : (tape : Tape) → List Bool → List (Alphabet tape)
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def toBoolWord : (tape : Tape) → List (Alphabet tape) → List Bool
  | .inl (.inl _), word => word
  | .inl (.inr _), word => word
  | .inr _, word => word

def fromBoolTapes (base : Tape → List Bool) : (tape : Tape) → List (Alphabet tape) :=
  fun tape => boolWord tape (base tape)

def toBoolTapes (base : (tape : Tape) → List (Alphabet tape)) : Tape → List Bool :=
  fun tape => toBoolWord tape (base tape)

@[simp] theorem toBoolWord_boolWord (tape : Tape) (word : List Bool) :
    toBoolWord tape (boolWord tape word) = word := by
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem boolWord_toBoolWord (tape : Tape) (word : List (Alphabet tape)) :
    boolWord tape (toBoolWord tape word) = word := by
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

@[simp] theorem toBool_fromBool (base : Tape → List Bool) :
    toBoolTapes (fromBoolTapes base) = base := by
  funext tape
  exact toBoolWord_boolWord tape (base tape)

@[simp] theorem fromBool_toBool (base : (tape : Tape) → List (Alphabet tape)) :
    fromBoolTapes (toBoolTapes base) = base := by
  funext tape
  exact boolWord_toBoolWord tape (base tape)

@[simp] theorem fromBoolTapes_update (base : Tape → List Bool) (tape : Tape) (word : List Bool) :
    fromBoolTapes (Function.update base tape word) =
      Function.update (fromBoolTapes base) tape (boolWord tape word) := by
  funext k
  by_cases h : k = tape
  · subst k
    simp [fromBoolTapes]
  · simp [fromBoolTapes, h]

@[simp] theorem toBoolTapes_update (base : (tape : Tape) → List (Alphabet tape))
    (tape : Tape) (word : List (Alphabet tape)) :
    toBoolTapes (Function.update base tape word) =
      Function.update (toBoolTapes base) tape (toBoolWord tape word) := by
  funext k
  by_cases h : k = tape
  · subst k
    simp [toBoolTapes]
  · simp [toBoolTapes, h]

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

def clearRegister (state : State ρ d) : State ρ d :=
  (MachineExpanderTable.clearRegister state.1, state.2)

@[simp] theorem registerStates_reset (state : State ρ d) :
    registerStates ρ d (((registerStates ρ d).symm state).1, none) =
      clearRegister state := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

@[simp] theorem caller_clearRegister (state : State ρ d) :
    caller (clearRegister state) = caller state := rfl

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).1.2 = state.1.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.1.2 = none := rfl

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

def emittedWord {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) : K → List Bool :=
  Function.update base target ((encodeWord value).reverse ++ base target)

@[simp] theorem emittedWord_target {K : Type} [DecidableEq K]
    (target : K) (base : K → List Bool) (value : Nat) :
    emittedWord target base value target = (encodeWord value).reverse ++ base target := by
  simp [emittedWord]

variable {ρ : Type} [Fintype ρ] {d : Nat}

@[simp] theorem program_firstEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.firstEmit label) =
      Emitter.statement (firstPlan ρ d) (fun _ : Fin 1 => Tape.inputVertex)
        .emitScratch .queryReverse Label.firstEmit (some Label.firstReverse) label := rfl

@[simp] theorem program_secondEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (degree d)) :
    program (ρ := ρ) positive H (.secondEmit label) =
      Emitter.statement (secondPlan ρ d) (fun _ : Fin 1 => Tape.quotientFirst)
        .emitScratch .queryReverse Label.secondEmit (some Label.secondReverse) label := rfl

@[simp] theorem program_outputEmit (positive : 0 < d) (H : Table (cloudSize d) d)
    (label : Emitter.Label 3 (rowFactor d)) :
    program (ρ := ρ) positive H (.outputEmit label) =
      Emitter.statement (outputPlan ρ d) (fun _ : Fin 1 => Tape.quotientSecond)
        .emitScratch .output Label.outputEmit (some (Label.cleanup 0)) label := rfl

end DFVSGames.Foundations.Complexity.MachineExpanderRow

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRowLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

def lookupResultTapes (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) : K → List Bool :=
  MachinePreservingLookup.initialTapes (ports ∘ lookupTape) base 0 indexSuffix []
    (encodeWord value ++ base (ports .lookupOutput))

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

@[simp] theorem dirtyTape_zero : dirtyTape 0 = .queryIndex := rfl
@[simp] theorem dirtyTape_one : dirtyTape 1 = .lookupOutput := rfl
@[simp] theorem dirtyTape_two : dirtyTape 2 = .quotientFirst := rfl
@[simp] theorem dirtyTape_three : dirtyTape 3 = .quotientSecond := rfl
@[simp] theorem dirtyTape_four : dirtyTape 4 = .remainderFirst := rfl
@[simp] theorem dirtyTape_five : dirtyTape 5 = .remainderSecond := rfl

variable {K Λ ρ : Type} [DecidableEq K]

def cleanupTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update base (ports .queryIndex) [])
            (ports .lookupOutput) [])
          (ports .quotientFirst) [])
        (ports .quotientSecond) [])
      (ports .remainderFirst) [])
    (ports .remainderSecond) []

@[simp] theorem cleanupTapes_dirty (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) (i : Fin 6) :
    cleanupTapes ports base (ports (dirtyTape i)) = [] := by
  fin_cases i <;>
    simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_table (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .table) = base (ports .table) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_inputVertex (ports : Tape → K)
    (distinct : Function.Injective ports) (base : K → List Bool) :
    cleanupTapes ports base (ports .inputVertex) = base (ports .inputVertex) := by
  simp [cleanupTapes, distinct.eq_iff]

@[simp] theorem cleanupTapes_output (ports : Tape → K) (distinct : Function.Injective ports)
    (base : K → List Bool) :
    cleanupTapes ports base (ports .output) = base (ports .output) := by
  simp [cleanupTapes, distinct.eq_iff]

variable [Fintype ρ] {d : Nat}

def initializedTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update
      (Function.update
        (Function.update base (ports .quotientFirst) (false :: base (ports .quotientFirst)))
        (ports .quotientSecond) (false :: base (ports .quotientSecond)))
      (ports .remainderFirst) (false :: base (ports .remainderFirst)))
    (ports .remainderSecond) (false :: base (ports .remainderSecond))

def clearedQueryTapes (ports : Tape → K) (base : K → List Bool) : K → List Bool :=
  Function.update
    (Function.update base (ports .queryIndex) (base (ports .queryIndex)).tail)
    (ports .lookupOutput) (base (ports .lookupOutput)).tail

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

structure RowData (v d : Nat) where
  oldTable : Table v (degree d)
  smallTable : Table (cloudSize d) d
  inputVertex : Fin v
  inputCloud : Fin (cloudSize d)
  inputPort : Fin (degree d)

def rowData {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) : RowData v d :=
  ⟨G, H, vertex, cloud, port⟩

namespace RowData

variable {v d : Nat} (r : RowData v d)

def control0 : Control d := start r.smallTable r.inputCloud r.inputPort
def firstRow : Fin (v * degree d) := rowIndex v (degree d) (r.inputVertex, firstOffset r.control0)
def firstValue : Nat := (reverseIndex r.oldTable r.firstRow).val
def firstPair : Fin v × Fin (degree d) := lookup r.oldTable (r.inputVertex, firstOffset r.control0)
def firstVertex : Fin v := r.firstPair.1
def firstReturn : Fin (degree d) := r.firstPair.2
def control1 : Control d := receiveFirst r.control0 r.firstReturn
def secondRow : Fin (v * degree d) := rowIndex v (degree d) (r.firstVertex, secondOffset r.control1)
def secondValue : Nat := (reverseIndex r.oldTable r.secondRow).val
def secondPair : Fin v × Fin (degree d) := lookup r.oldTable (r.firstVertex, secondOffset r.control1)
def secondVertex : Fin v := r.secondPair.1
def secondReturn : Fin (degree d) := r.secondPair.2
def control2 : Control d := receiveSecond r.smallTable r.control1 r.secondReturn
def query1 : Nat := firstAddress r.inputVertex.val r.control0
def query2 : Nat := secondAddress r.firstVertex.val r.control1
def finalValue : Nat := outputAddress r.secondVertex.val r.control2

@[simp] theorem firstValue_div_degree : r.firstValue / degree d = r.firstVertex.val := rfl
@[simp] theorem firstValue_mod_degree : r.firstValue % degree d = r.firstReturn.val := rfl
@[simp] theorem secondValue_div_degree : r.secondValue / degree d = r.secondVertex.val := rfl
@[simp] theorem secondValue_mod_degree : r.secondValue % degree d = r.secondReturn.val := rfl

end RowData

variable {v d : Nat}

def frameContents (r : RowData v d) (output : List Bool)
    (qr qi lo q1 q2 r1 r2 : List Bool) : Tape → List Bool
  | .inputVertex => encodeWord r.inputVertex.val
  | .table => encodeWords (rotationWords r.oldTable)
  | .output => output
  | .queryReverse => qr
  | .queryIndex => qi
  | .lookupOutput => lo
  | .quotientFirst => q1
  | .quotientSecond => q2
  | .remainderFirst => r1
  | .remainderSecond => r2
  | _ => []

def frame0 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  frameContents r output [] [] [] [] [] [] []
def frame1 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  initializedTapes id (frame0 r output)
def frame2 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .queryReverse (frame1 r output) r.query1
def frame3 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .queryReverse .queryIndex (frame2 r output) []
    (encodeWord r.query1)
def frame4 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  lookupResultTapes id (frame3 r output) r.firstValue []
def frame5 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  divisionOutput d id .quotientFirst .remainderFirst (frame4 r output) r.firstValue [] [] []
def frame6 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  clearedQueryTapes id (frame5 r output)
def frame7 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .queryReverse (frame6 r output) r.query2
def frame8 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  Reduction.MachineTransfer.tapesAt .queryReverse .queryIndex (frame7 r output) []
    (encodeWord r.query2)
def frame9 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  lookupResultTapes id (frame8 r output) r.secondValue []
def frame10 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  divisionOutput d id .quotientSecond .remainderSecond (frame9 r output) r.secondValue [] [] []
def frame11 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  emittedWord .output (frame10 r output) r.finalValue
def frame12 (r : RowData v d) (output : List Bool) : Tape → List Bool :=
  cleanupTapes id (frame11 r output)

theorem lookupResultTapes_id_eq_inline_MachineExpanderRowFrames (base : Tape → List Bool)
    (value : Nat) (suffix : List Bool) :
    lookupResultTapes id base value suffix =
      Function.update
        (Function.update (Function.update base .queryIndex (encodeWord 0 ++ suffix))
          .lookupWork [])
        .lookupOutput (encodeWord value ++ base .lookupOutput) := rfl

@[simp] theorem frame1_eq (r : RowData v d) (output : List Bool) :
    frame1 r output = frameContents r output [] [] []
      (encodeWord 0) (encodeWord 0) (encodeWord 0) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame1, frame0, frameContents, initializedTapes, encodeWord]

@[simp] theorem frame2_eq (r : RowData v d) (output : List Bool) :
    frame2 r output = frameContents r output (encodeWord r.query1).reverse [] []
      (encodeWord 0) (encodeWord 0) (encodeWord 0) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame2, frameContents, emittedWord]

@[simp] theorem frame3_eq (r : RowData v d) (output : List Bool) :
    frame3 r output = frameContents r output [] (encodeWord r.query1) []
      (encodeWord 0) (encodeWord 0) (encodeWord 0) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame3, frameContents, Reduction.MachineTransfer.tapesAt]

@[simp] theorem frame4_eq (r : RowData v d) (output : List Bool) :
    frame4 r output = frameContents r output [] (encodeWord 0) (encodeWord r.firstValue)
      (encodeWord 0) (encodeWord 0) (encodeWord 0) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame4, lookupResultTapes_id_eq_inline_MachineExpanderRowFrames, frameContents]

@[simp] theorem frame5_eq (r : RowData v d) (output : List Bool) :
    frame5 r output = frameContents r output [] (encodeWord 0) (encodeWord 0)
      (encodeWord r.firstVertex.val) (encodeWord 0)
      (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame5, divisionOutput, MachineFixedDivMod.unaryTapes,
    MachineFixedDivMod.tapes, MachineCopy.forkTapes, frameContents]

@[simp] theorem frame6_eq (r : RowData v d) (output : List Bool) :
    frame6 r output = frameContents r output [] [] [] (encodeWord r.firstVertex.val)
      (encodeWord 0) (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame6, clearedQueryTapes, frameContents, encodeWord]

@[simp] theorem frame7_eq (r : RowData v d) (output : List Bool) :
    frame7 r output = frameContents r output (encodeWord r.query2).reverse [] []
      (encodeWord r.firstVertex.val) (encodeWord 0)
      (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame7, emittedWord, frameContents]

@[simp] theorem frame8_eq (r : RowData v d) (output : List Bool) :
    frame8 r output = frameContents r output [] (encodeWord r.query2) []
      (encodeWord r.firstVertex.val) (encodeWord 0)
      (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame8, Reduction.MachineTransfer.tapesAt, frameContents]

@[simp] theorem frame9_eq (r : RowData v d) (output : List Bool) :
    frame9 r output = frameContents r output [] (encodeWord 0) (encodeWord r.secondValue)
      (encodeWord r.firstVertex.val) (encodeWord 0)
      (encodeWord r.firstReturn.val) (encodeWord 0) := by
  funext tape
  cases tape <;> simp [frame9, lookupResultTapes_id_eq_inline_MachineExpanderRowFrames, frameContents]

@[simp] theorem frame10_eq (r : RowData v d) (output : List Bool) :
    frame10 r output = frameContents r output [] (encodeWord 0) (encodeWord 0)
      (encodeWord r.firstVertex.val) (encodeWord r.secondVertex.val)
      (encodeWord r.firstReturn.val) (encodeWord r.secondReturn.val) := by
  funext tape
  cases tape <;> simp [frame10, divisionOutput, MachineFixedDivMod.unaryTapes,
    MachineFixedDivMod.tapes, MachineCopy.forkTapes, frameContents]

@[simp] theorem frame11_eq (r : RowData v d) (output : List Bool) :
    frame11 r output = frameContents r ((encodeWord r.finalValue).reverse ++ output)
      [] (encodeWord 0) (encodeWord 0)
      (encodeWord r.firstVertex.val) (encodeWord r.secondVertex.val)
      (encodeWord r.firstReturn.val) (encodeWord r.secondReturn.val) := by
  funext tape
  cases tape <;> simp [frame11, emittedWord, frameContents]

@[simp] theorem frame12_eq (r : RowData v d) (output : List Bool) :
    frame12 r output = frameContents r ((encodeWord r.finalValue).reverse ++ output)
      [] [] [] [] [] [] [] := by
  funext tape
  cases tape <;> simp [frame12, cleanupTapes, frameContents]

@[simp] theorem frame0_inputVertex (r : RowData v d) (output : List Bool) :
    frame0 r output .inputVertex = encodeWord r.inputVertex.val := rfl

@[simp] theorem frame0_table (r : RowData v d) (output : List Bool) :
    frame0 r output .table = encodeWords (rotationWords r.oldTable) := rfl

@[simp] theorem frame0_output (r : RowData v d) (output : List Bool) :
    frame0 r output .output = output := rfl

@[simp] theorem frame1_inputVertex (r : RowData v d) (output : List Bool) :
    frame1 r output .inputVertex = encodeWord r.inputVertex.val := by simp [frameContents]

@[simp] theorem frame1_emitScratch (r : RowData v d) (output : List Bool) :
    frame1 r output .emitScratch = [] := by simp [frameContents]

@[simp] theorem frame2_queryReverse (r : RowData v d) (output : List Bool) :
    frame2 r output .queryReverse = (encodeWord r.query1).reverse := by simp [frameContents]

@[simp] theorem frame2_queryIndex (r : RowData v d) (output : List Bool) :
    frame2 r output .queryIndex = [] := by simp [frameContents]

@[simp] theorem frame3_table (r : RowData v d) (output : List Bool) :
    frame3 r output .table = encodeWords (rotationWords r.oldTable) := by simp [frameContents]

@[simp] theorem frame3_lookupRestore (r : RowData v d) (output : List Bool) :
    frame3 r output .lookupRestore = [] := by simp [frameContents]

@[simp] theorem frame3_lookupWork (r : RowData v d) (output : List Bool) :
    frame3 r output .lookupWork = [] := by simp [frameContents]

@[simp] theorem frame3_lookupOutput (r : RowData v d) (output : List Bool) :
    frame3 r output .lookupOutput = [] := by simp [frameContents]

@[simp] theorem frame3_queryIndex (r : RowData v d) (output : List Bool) :
    frame3 r output .queryIndex = encodeWord r.query1 := by simp [frameContents]

@[simp] theorem frame4_lookupOutput (r : RowData v d) (output : List Bool) :
    frame4 r output .lookupOutput = encodeWord r.firstValue := by simp [frameContents]

@[simp] theorem frame4_quotientFirst (r : RowData v d) (output : List Bool) :
    frame4 r output .quotientFirst = encodeWord 0 := by simp [frameContents]

@[simp] theorem frame4_remainderFirst (r : RowData v d) (output : List Bool) :
    frame4 r output .remainderFirst = encodeWord 0 := by simp [frameContents]

@[simp] theorem frame6_quotientFirst (r : RowData v d) (output : List Bool) :
    frame6 r output .quotientFirst = encodeWord r.firstVertex.val := by simp [frameContents]

@[simp] theorem frame6_emitScratch (r : RowData v d) (output : List Bool) :
    frame6 r output .emitScratch = [] := by simp [frameContents]

@[simp] theorem frame7_queryReverse (r : RowData v d) (output : List Bool) :
    frame7 r output .queryReverse = (encodeWord r.query2).reverse := by simp [frameContents]

@[simp] theorem frame7_queryIndex (r : RowData v d) (output : List Bool) :
    frame7 r output .queryIndex = [] := by simp [frameContents]

@[simp] theorem frame8_table (r : RowData v d) (output : List Bool) :
    frame8 r output .table = encodeWords (rotationWords r.oldTable) := by simp [frameContents]

@[simp] theorem frame8_lookupRestore (r : RowData v d) (output : List Bool) :
    frame8 r output .lookupRestore = [] := by simp [frameContents]

@[simp] theorem frame8_lookupWork (r : RowData v d) (output : List Bool) :
    frame8 r output .lookupWork = [] := by simp [frameContents]

@[simp] theorem frame8_lookupOutput (r : RowData v d) (output : List Bool) :
    frame8 r output .lookupOutput = [] := by simp [frameContents]

@[simp] theorem frame8_queryIndex (r : RowData v d) (output : List Bool) :
    frame8 r output .queryIndex = encodeWord r.query2 := by simp [frameContents]

@[simp] theorem frame9_lookupOutput (r : RowData v d) (output : List Bool) :
    frame9 r output .lookupOutput = encodeWord r.secondValue := by simp [frameContents]

@[simp] theorem frame9_quotientSecond (r : RowData v d) (output : List Bool) :
    frame9 r output .quotientSecond = encodeWord 0 := by simp [frameContents]

@[simp] theorem frame9_remainderSecond (r : RowData v d) (output : List Bool) :
    frame9 r output .remainderSecond = encodeWord 0 := by simp [frameContents]

@[simp] theorem frame10_quotientSecond (r : RowData v d) (output : List Bool) :
    frame10 r output .quotientSecond = encodeWord r.secondVertex.val := by simp [frameContents]

@[simp] theorem frame10_emitScratch (r : RowData v d) (output : List Bool) :
    frame10 r output .emitScratch = [] := by simp [frameContents]

@[simp] theorem frame10_output (r : RowData v d) (output : List Bool) :
    frame10 r output .output = output := by simp [frameContents]

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem caller_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    caller (boundaryState positive H ambient position) = ambient := rfl

@[simp] theorem prepareState_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    prepareState positive H (boundaryState positive H ambient position) =
      boundaryState positive H ambient position := rfl

@[simp] theorem clearRegister_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    clearRegister (boundaryState positive H ambient position) =
      boundaryState positive H ambient position := rfl

@[simp] theorem caller_prepareState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (prepareState positive H state) = caller state := rfl

@[simp] theorem caller_resetState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (resetState positive H state) = caller state := rfl

@[simp] theorem caller_clearRegister (state : State ρ d) :
    caller (clearRegister state) = caller state := rfl

@[simp] theorem caller_advancePositionState (positive : 0 < d) (state : State ρ d) :
    caller (advancePositionState positive state) = caller state := rfl

@[simp] theorem caller_resetPositionState (positive : 0 < d) (state : State ρ d) :
    caller (resetPositionState positive state) = caller state := rfl

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open DFVSGames.Foundations.Complexity

variable {v d : Nat}

def globalIndex (vertex : Fin v) (position : Fin (rowFactor d)) :
    Fin ((v * cloudSize d) * degree d) :=
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  rowIndex (v * cloudSize d) (degree d)
    (rowIndex v (cloudSize d) (vertex, pair.1), pair.2)

theorem globalIndex_val (vertex : Fin v) (position : Fin (rowFactor d)) :
    (globalIndex vertex position).val = position.val + rowFactor d * vertex.val := by
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  have hp := congrArg Fin.val
    ((rowIndex (cloudSize d) (degree d)).apply_symm_apply position)
  change pair.2.val + degree d * pair.1.val = position.val at hp
  change pair.2.val + degree d * (pair.1.val + cloudSize d * vertex.val) = _
  calc
    _ = (pair.2.val + degree d * pair.1.val) + rowFactor d * vertex.val := by
      dsimp only [rowFactor]
      ring
    _ = position.val + rowFactor d * vertex.val := by rw [hp]

def rowValue (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) : Nat :=
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  let result := evaluateRow G H vertex pair.1 pair.2
  outputAddress result.1.val result.2

theorem rowValue_eq_reverseIndex (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) :
    rowValue G H vertex position = (reverseIndex (step G H) (globalIndex vertex position)).val := by
  exact outputAddress_eq_step_reverseIndex G H vertex
    ((rowIndex (cloudSize d) (degree d)).symm position).1
    ((rowIndex (cloudSize d) (degree d)).symm position).2

def vertexWords (G : Table v (degree d)) (H : Table (cloudSize d) d) (vertex : Fin v) :
    List Nat := List.ofFn (rowValue G H vertex)

def generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d) : List Nat :=
  (List.ofFn (vertexWords G H)).flatten

@[simp] theorem vertexWords_length (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) : (vertexWords G H vertex).length = rowFactor d := by
  simp [vertexWords]

@[simp] theorem vertexWords_drop_full (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) : (vertexWords G H vertex).drop (rowFactor d) = [] := by
  apply List.drop_eq_nil_of_le
  simp

theorem rotationWords_eq_ofFn {n q : Nat} (G : Table n q) :
    rotationWords G = List.ofFn (fun i : Fin (n * q) => (reverseIndex G i).val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_ofFn]
    exact rotationWords_getElem G i (by simpa only [rotationWords_length] using hi)

theorem rowCount_eq : v * rowFactor d = (v * cloudSize d) * degree d :=
  (Nat.mul_assoc v (cloudSize d) (degree d)).symm

theorem generatedWords_eq_flat_ofFn (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    generatedWords G H = List.ofFn (fun i : Fin (v * rowFactor d) =>
      (reverseIndex (step G H) (Fin.cast rowCount_eq i)).val) := by
  rw [List.ofFn_mul]
  unfold generatedWords vertexWords
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext vertex
  apply congrArg List.ofFn
  funext position
  rw [rowValue_eq_reverseIndex]
  apply congrArg (fun i : Fin ((v * cloudSize d) * degree d) =>
    (reverseIndex (step G H) i).val)
  apply Fin.ext
  rw [globalIndex_val]
  change position.val + rowFactor d * vertex.val = vertex.val * rowFactor d + position.val
  ac_rfl

theorem generatedWords_eq_rotationWords (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    generatedWords G H = rotationWords (step G H) := by
  rw [generatedWords_eq_flat_ofFn]
  exact (ofFn_cast_inline_ExpanderTableEnumeration (rowCount_eq (v := v) (d := d))
    (fun i => (reverseIndex (step G H) i).val)).trans
    (rotationWords_eq_ofFn (step G H)).symm

@[simp] theorem generatedWords_length (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (generatedWords G H).length = v * rowFactor d := by
  rw [generatedWords_eq_rotationWords, rotationWords_length]
  exact rowCount_eq.symm

def priorVertices (G : Table v (degree d)) (H : Table (cloudSize d) d) (count : Nat) :
    List Nat := ((List.ofFn (vertexWords G H)).take count).flatten

@[simp] theorem priorVertices_zero (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    priorVertices G H 0 = [] := by simp [priorVertices]

@[simp] theorem priorVertices_full (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    priorVertices G H v = generatedWords G H := by
  unfold priorVertices generatedWords
  rw [List.take_of_length_le (by simp)]

def accumulate (values : List Nat) (initial : List Bool) : List Bool :=
  values.foldl (fun accumulator value => (encodeWord value).reverse ++ accumulator) initial

end DFVSGames.Foundations.PCP.ExpanderTableEnumeration

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def tableRowData {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Position d) : MachineExpanderRow.RowData v d :=
  MachineExpanderRow.rowData G H vertex (positionPair position).1 (positionPair position).2

variable {ρ : Type} [Fintype ρ] {v d : Nat}

def rowAfterState (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) : State ρ d :=
  (MachineExpanderRow.divisionState positive (caller state)
    (tableRowData G H vertex state.2).control2 none, state.2)

omit [Fintype ρ] in
@[simp] theorem rowAfterState_position (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) :
    (rowAfterState positive G H vertex state).2 = state.2 := rfl

omit [Fintype ρ] in
@[simp] theorem caller_rowAfterState (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) :
    caller (rowAfterState positive G H vertex state) = caller state := rfl

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderTableLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def oldTableWord {v d : Nat} (G : Table v (degree d)) : List Bool :=
  encodeWords (rotationWords G)

def accumulatedVertices {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) : List Bool :=
  accumulate (priorVertices G H current) []

@[simp] theorem accumulatedVertices_zero {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H 0 = [] := by
  simp [accumulatedVertices, accumulate]

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).2 = state.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.2 = none := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def timeCoefficient (d : Nat) : Nat :=
  rowFactor d * (rowFactor d + 1) + 82 * rowFactor d + 5

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (timeCoefficient d) * (Polynomial.X + 1) ^ 2

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def cycleWords (remaining : Nat) (word current vertex count result suffix : List Bool) :
    Tape → List Bool
  | .inl (.inl .table) => word
  | .inl (.inl .inputVertex) => vertex
  | .inl (.inr .vertexCount) => count
  | .inl (.inr .result) => result
  | .inr .remainingLevel => encodeWord remaining ++ suffix
  | .inr .currentSize => current
  | _ => []

def cycleTapes (remaining : Nat) (word current vertex count result suffix : List Bool) :
    (tape : Tape) → List (Alphabet tape) :=
  fromBoolTapes (cycleWords remaining word current vertex count result suffix)

@[simp] theorem toBool_cycleTapes (remaining : Nat)
    (word current vertex count result suffix : List Bool) :
    toBoolTapes (cycleTapes remaining word current vertex count result suffix) =
      cycleWords remaining word current vertex count result suffix := toBool_fromBool _

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

noncomputable def resizeCost {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : Nat :=
  (MachineExpanderTable.timePolynomial d).eval (MachineExpanderTable.oldTableWord G).length +
    6 * v + (MachineExpanderTable.oldTableWord G).length +
    2 * (encodeWords (rotationWords (step G H))).length + 15

noncomputable def resizeSum {d : Nat} (H : Table (cloudSize d) d) (level : Nat) : Nat :=
  ∑ i ∈ Finset.range level, resizeCost (family H i) H

@[simp] theorem resizeSum_zero {d : Nat} (H : Table (cloudSize d) d) :
    resizeSum H 0 = 0 := by simp [resizeSum]

noncomputable def familyBudget {d : Nat} (H : Table (cloudSize d) d) (level : Nat) : Nat :=
  resizeSum H level + level + 3

@[simp] theorem familyBudget_zero {d : Nat} (H : Table (cloudSize d) d) :
    familyBudget H 0 = 3 := by simp [familyBudget]

end DFVSGames.Foundations.Complexity.MachineExpanderFamilyBounds

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineExpanderFamilyLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem caller_initialState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) : caller (initialState positive H ambient) = ambient := rfl

@[simp] theorem caller_normalizeState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (normalizeState positive H state) = caller state := rfl

@[simp] theorem clearRegister_initialState (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) :
    clearRegister (initialState positive H ambient) = initialState positive H ambient := rfl

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineExpanderFamilyBounds

theorem baseDegree_cloud_growth :
    cloudSize PCP.Expanders.baseDegree = PCP.ExpanderFamily.growth := by
  unfold cloudSize degree PCP.ExpanderFamily.growth
  ring

theorem baseDegree_cloud_gt_one : 1 < cloudSize PCP.Expanders.baseDegree := by
  rw [baseDegree_cloud_growth]
  exact PCP.ExpanderFamily.growth_gt_one

theorem baseDegree_positive : 0 < PCP.Expanders.baseDegree := by
  have h := baseDegree_cloud_gt_one
  unfold cloudSize degree at h
  by_contra hn
  have hz : PCP.Expanders.baseDegree = 0 := by omega
  rw [hz] at h
  norm_num at h

end DFVSGames.Foundations.Complexity.MachineExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev SmallTable := Table (cloudSize fixedDegree) fixedDegree
abbrev Tape := MachineExpanderFamily.Tape ⊕ MachineCeilingPower.Tape
abbrev Alphabet (_ : Tape) := Bool
abbrev Label := MachineExpanderFamily.Label fixedDegree ⊕ MachineCeilingPower.Label
abbrev State (ρ : Type) := MachineExpanderFamily.State ρ fixedDegree × (Bool × Option Bool)

def familyTape (tape : MachineExpanderFamily.Tape) : Tape := .inl tape

def familyView : Tape → Option MachineExpanderFamily.Tape
  | .inl tape => some tape
  | .inr _ => none

@[simp] theorem familyView_left (tape : MachineExpanderFamily.Tape) :
    familyView (familyTape tape) = some tape := rfl

def ceilingTape : MachineCeilingPower.Tape → Tape
  | .level => .inl (.inr .remainingLevel)
  | tape => .inr tape

def ceilingView : Tape → Option MachineCeilingPower.Tape
  | .inl (.inr .remainingLevel) => some .level
  | .inl _ => none
  | .inr .level => none
  | .inr tape => some tape

@[simp] theorem ceilingView_left (tape : MachineCeilingPower.Tape) :
    ceilingView (ceilingTape tape) = some tape := by
  cases tape <;> rfl

def familyLabel (label : MachineExpanderFamily.Label fixedDegree) : Label := .inl label
def ceilingLabel (label : MachineCeilingPower.Label) : Label := .inr label
def familyEntry : Label := .inl (.inr .initialize_)

def ceilingStates (ρ : Type) :
    MachineCeilingPower.State (MachineExpanderFamily.State ρ fixedDegree) ≃ State ρ :=
  Equiv.prodAssoc _ _ _

@[simp] theorem ceilingStates_apply (ρ : Type)
    (state : MachineCeilingPower.State (MachineExpanderFamily.State ρ fixedDegree)) :
    ceilingStates ρ state = (state.1.1, (state.1.2, state.2)) := rfl

variable {ρ : Type} [Fintype ρ]

def familySource (H : SmallTable) : MachineExpanderFamily.Label fixedDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet
      (MachineExpanderFamily.Label fixedDegree) (State ρ) :=
  MachineStateFrame.frameProgram (τ := Bool × Option Bool)
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)

def ceilingSource : MachineCeilingPower.Label →
    TM2.Stmt MachineCeilingPower.Alphabet MachineCeilingPower.Label (State ρ) :=
  MachineStateEquiv.program (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth)

def program (H : SmallTable) : Label → TM2.Stmt Alphabet Label (State ρ)
  | .inl label =>
    MachineCloudPadding.Placement.statement familyTape familyLabel none (familySource H label)
  | .inr label =>
    MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
      (ceilingSource (ρ := ρ) label)

@[simp] theorem program_family (H : SmallTable)
    (label : MachineExpanderFamily.Label fixedDegree) :
    program (ρ := ρ) H (familyLabel label) =
      MachineCloudPadding.Placement.statement familyTape familyLabel none
        (familySource H label) := rfl

@[simp] theorem program_ceiling (H : SmallTable) (label : MachineCeilingPower.Label) :
    program (ρ := ρ) H (ceilingLabel label) =
      MachineCloudPadding.Placement.statement ceilingTape ceilingLabel (some familyEntry)
        (ceilingSource (ρ := ρ) label) := rfl

def initialTapes (requested : Nat) : Tape → List Bool
  | .inr .input => encodeWord requested
  | _ => []

def retainedCeilingTapes (requested : Nat) : MachineCeilingPower.Tape → List Bool :=
  MachineCeilingPower.memory (encodeWord requested) []
    (encodeWord (PCP.PreprocessingLevels.paddedSize requested)) [] [] [] [] []

def handoffTapes (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

def finalTapes (H : SmallTable) (requested : Nat) : Tape → List Bool
  | .inl tape => MachineExpanderFamily.toBoolTapes
      (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []) tape
  | .inr tape => retainedCeilingTapes requested tape

@[simp] theorem initialTapes_input (requested : Nat) :
    initialTapes requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_input (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .input) = encodeWord requested := rfl

@[simp] theorem finalTapes_power (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .power) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := rfl

end DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily
end

section

namespace DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily

open Turing
open MachineCloudPadding
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

@[simp] theorem handoffTapes_level (requested : Nat) :
    handoffTapes requested (ceilingTape .level) =
      encodeWord (PCP.PreprocessingLevels.boundedLevel requested) := by
  simp [handoffTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
    MachineEmbedding.tapes]

@[simp] theorem handoffTapes_level_shadow (requested : Nat) :
    handoffTapes requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_level_shadow (H : SmallTable) (requested : Nat) :
    finalTapes H requested (.inr .level) = [] := rfl

@[simp] theorem finalTapes_remainingLevel (H : SmallTable) (requested : Nat) :
    finalTapes H requested (ceilingTape .level) = encodeWord 0 := by
  simp [finalTapes, ceilingTape, MachineExpanderFamily.toBoolTapes,
    MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
    MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
    MachineEmbedding.tapes]

end DFVSGames.Foundations.Complexity.MachinePaddedExpanderFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachinePaddedExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev NativeTape := MachinePaddedExpanderFamily.Tape

end DFVSGames.Foundations.Complexity.MachineRegularFamily
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineDummyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineDummyRows

open Turing
open PCP.GraphTables
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

def trueRelation : RelationTable := Vector.replicate 4096 true

end DFVSGames.Foundations.Complexity.MachineDummyRows

end

section

namespace DFVSGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

def rowBits (table : Table n d) (v : Fin n) (p : Fin d) : List Bool :=
  encodeWord v.val ++ encodeWord (table.reverseIndex[rowIndex n d (v, p)]).val ++
    encodeWords (GraphTables.relationWords table.relations[rowIndex n d (v, p)])

def vertexBits (table : Table n d) (v : Fin n) : List Bool :=
  (List.ofFn (fun p : Fin d => rowBits table v p)).flatten

theorem rowBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) (p : Fin d) :
    rowBits (PreprocessingPaddingTables.pad table h) (v.castLE h) p = rowBits table v p := by
  unfold rowBits
  rw [PreprocessingPaddingTables.reverseIndex_pad_old,
    PreprocessingPaddingTables.relations_pad_old]
  have he : (rowIndex m d ((rotation table (v, p)).1.castLE h,
      (rotation table (v, p)).2)).val = (table.reverseIndex[rowIndex n d (v, p)]).val := by
    rw [← rowIndex_rotation]
    rfl
  rw [he]
  rfl

@[simp] theorem vertexBits_pad_old (table : Table n d) (h : n ≤ m) (v : Fin n) :
    vertexBits (PreprocessingPaddingTables.pad table h) (v.castLE h) = vertexBits table v := by
  simp only [vertexBits, rowBits_pad_old]

end DFVSGames.Foundations.PCP.PreprocessingPaddingWords

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingRegularWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

def actualRow (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    GraphTables.DartRow (vertexCount t padding) (vertexCount t padding * (q + 1)) :=
  (PortTables.flatRows (ofCloudTables t padding tables))[
    PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]

theorem actualRow_eq (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    actualRow t padding tables x p =
      ⟨vertexOrder t padding x,
        (ofCloudTables t padding tables).reverseIndex[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)],
        (ofCloudTables t padding tables).relations[
          PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p)]⟩ := by
  simp only [actualRow, PortTables.flatRows, Vector.getElem_ofFn,
    Fin.getElem_fin, Fin.eta, Equiv.symm_apply_apply]

@[simp] theorem actualRow_tail (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    (actualRow t padding tables x p).tail.val = (vertexOrder t padding x).val := by
  rw [actualRow_eq]

@[simp] theorem inherited_original_reverse (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).reverseIndex.val =
      (q + 1) * t.rows[e].reverseIndex.val + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inl e), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inl (GraphTables.reverseAt t.rows e)), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, vertexOrder_original, portOrder_inherited]
  exact Nat.add_comm _ _

@[simp] theorem inherited_dummy_reverse (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).reverseIndex.val =
      (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q := by
  rw [actualRow_eq]
  change ((ofCloudTables t padding tables).reverseIndex[PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))]).val = _
  rw [← PortTables.rowIndex_rotation, rotation_ofCloudTables]
  change (PortTables.rowIndex _ _
    (vertexOrder t padding (.inr ⟨v, j⟩), portOrder q (.inr ()))).val = _
  rw [PortTables.rowIndex_val, PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    portOrder_inherited]
  exact Nat.add_comm _ _

theorem relation_ext_inline_PreprocessingRegularWords {r s : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt r a b = GraphTables.relationAt s a b) : r = s := by
  apply Vector.ext
  intro i hi
  simpa only [GraphTables.relationAt, Prod.eta, Equiv.apply_symm_apply,
    Fin.getElem_fin] using h (GraphTables.relationIndex.symm ⟨i, hi⟩).1
      (GraphTables.relationIndex.symm ⟨i, hi⟩).2

@[simp] theorem inherited_original_relation (e : Fin t.darts) :
    (actualRow t padding tables (.inl e) (.inr ())).relation = t.rows[e].relation := by
  rw [actualRow_eq]
  apply relation_ext_inline_PreprocessingRegularWords
  intro a b
  exact accepts_original t padding tables e a b

@[simp] theorem inherited_dummy_relation (v : Fin t.vertices) (j : Fin (padding v)) :
    (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())).relation =
      MachineDummyRows.trueRelation := by
  rw [actualRow_eq]
  apply relation_ext_inline_PreprocessingRegularWords
  intro a b
  have h := accepts_dummy t padding tables ⟨v, j⟩ a b
  simpa only [PortTables.accepts, MachineDummyRows.trueRelation,
    GraphTables.relationAt, Fin.getElem_fin, Vector.getElem_replicate] using h

end DFVSGames.Foundations.PCP.PreprocessingRegularWords

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables

abbrev Tape := Fin 27 ⊕ (MachineRegularMetadata.Extra ⊕ MachinePaddedExpanderFamily.Tape)

end DFVSGames.Foundations.Complexity.MachineRegularOriginalBody
end

section

namespace DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing MachineComposition

variable {LabelType : Type}

abbrev Tape := MachineRegularOriginalBody.Tape ⊕ Fin 2

instance tapeDecidableEq : DecidableEq Tape :=
  sumDecidableEq_inline_MachineRegularOwnerCleanup
    (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq (Fin 27)))
      (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq MachineRegularMetadata.Extra))
        (sumDecidableEq_inline_MachineRegularOwnerCleanup
          (sumDecidableEq_inline_MachineRegularOwnerCleanup
            (sumDecidableEq_inline_MachineRegularOwnerCleanup (inferInstanceAs (DecidableEq MachineExpanderRow.Tape))
              (inferInstanceAs (DecidableEq MachineExpanderTable.ExtraTape)))
            (inferInstanceAs (DecidableEq MachineExpanderFamily.ExtraTape)))
          (inferInstanceAs (DecidableEq MachineCeilingPower.Tape)))))
    (inferInstanceAs (DecidableEq (Fin 2)))

instance tapeBEq : BEq Tape where
  beq a b := decide (a = b)

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

def core (k : Fin 27) : Tape := .inl (.inl k)
def localRank : Tape := core 3
def count : Tape := core 4
def prefixTape : Tape := core 5
def rotor : Tape := core 7
def padding : Tape := .inl (.inr (.inl .padding))
def level : Tape := .inl (.inr (.inl .level))
def dummyFuel : Tape := .inr 0

def cleanupTapes : List Tape := [localRank, count, rotor, padding, level, dummyFuel]

def afterAddition (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  Function.update base prefixTape (encodeWord (d + o))

def finalTapes (base : Tape → List Bool) (d o : Nat) : Tape → List Bool :=
  MachineDrainMany.finalTapes cleanupTapes (afterAddition base d o)

theorem finalTapes_apply (base : Tape → List Bool) (d o : Nat) (k : Tape) :
    finalTapes base d o k =
      if k ∈ cleanupTapes then []
      else if k = prefixTape then encodeWord (d + o) else base k := by
  simp only [finalTapes, MachineDrainMany.finalTapes_apply, afterAddition,
    Function.update_apply]

@[simp] theorem finalTapes_prefix (base : Tape → List Bool) (d o : Nat) :
    finalTapes base d o prefixTape = encodeWord (d + o) := by
  simp [finalTapes_apply, cleanupTapes, prefixTape, localRank, count, rotor,
    padding, level, dummyFuel, core]

end DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_PreprocessingStageMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineTableSplit

open Turing MachineComposition

def resultTapes (n m : Nat) (rowsBits : List Bool) : Tape → List Bool :=
  tapes (encodeWords [n, m] ++ rowsBits) rowsBits (encodeWord n) (encodeWord m)

@[simp] theorem resultTapes_original (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 0 = encodeWords [n, m] ++ rowsBits := by
  simp [resultTapes, tapes]

@[simp] theorem resultTapes_work (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 1 = rowsBits := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_scratch (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 2 = [] := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_vertices (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 3 = encodeWord n := by simp [resultTapes, tapes]

@[simp] theorem resultTapes_darts (n m : Nat) (rowsBits : List Bool) :
    resultTapes n m rowsBits 4 = encodeWord m := by simp [resultTapes, tapes]

end DFVSGames.Foundations.Complexity.MachineTableSplit

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_GraphCounterFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Foundations.Complexity.PCPIterationMachine

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def program (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)) :
    Labels Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)
  | .inl false => MachineUnaryCounter.guard counter (.inr entry) (.inl true)
  | .inl true => .pop counter (fun state _ => (state.1, none)) .halt
  | .inr label => body label

omit [DecidableEq K] in
@[simp] theorem program_guard (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)) :
    program counter entry body (.inl false) =
      MachineUnaryCounter.guard counter (.inr entry) (.inl true) := rfl

end DFVSGames.Foundations.Complexity.PCPIterationMachine

namespace DFVSGames.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

def clauseSigns {n : Nat} (c : Clause n) : Signs :=
  ((c)[0].positive, (c)[1].positive, (c)[2].positive)

def clauseNames {n : Nat} (c : Clause n) : Names :=
  ((c)[0].variableIndex.val, (c)[1].variableIndex.val, (c)[2].variableIndex.val)

def nameWord (names : Names) : Slot → Nat
  | .first => names.1
  | .second => names.2.1
  | .third => names.2.2

def decodedLabel (a : GraphTables.Label) : InitialGraph.Label :=
  AlphabetRetraction.decode64 (labelOrder.symm a)

def incidencePredicate (signs : Signs) (slot : Slot)
    (clauseLabel variableLabel : InitialGraph.Label) : Bool :=
  InitialGraph.variableValid variableLabel &&
    (((literalValue signs.1 clauseLabel.1 ||
      literalValue signs.2.1 clauseLabel.2.1) ||
      literalValue signs.2.2 clauseLabel.2.2) &&
      decide (answerAt (InitialGraph.toClauseAnswer clauseLabel) slot = variableLabel.1))

def relationPredicate (signs : Signs) (slot : Slot) :
    Bool → GraphTables.Label → GraphTables.Label → Bool
  | false, a, b => incidencePredicate signs slot (decodedLabel a) (decodedLabel b)
  | true, a, b => incidencePredicate signs slot (decodedLabel b) (decodedLabel a)

def relationWordsFor (signs : Signs) (slot : Slot) (orientation : Bool) : List Nat :=
  relationWords (relationOf (relationPredicate signs slot orientation))

@[simp] theorem relationWordsFor_length (signs : Signs) (slot : Slot) (orientation : Bool) :
    (relationWordsFor signs slot orientation).length = 4096 := by
  exact relationWords_length _

def incidenceWords (n i : Nat) (names : Names) (signs : Signs)
    (slot : Slot) (orientation : Bool) : List Nat :=
  [if orientation then nameWord names slot else n + i,
    6 * i + 2 * (slotOrder slot).val + (if orientation then 0 else 1)] ++
      relationWordsFor signs slot orientation

def clauseWords (n i : Nat) (names : Names) (signs : Signs) : List Nat :=
  incidenceWords n i names signs .first false ++
  incidenceWords n i names signs .first true ++
  incidenceWords n i names signs .second false ++
  incidenceWords n i names signs .second true ++
  incidenceWords n i names signs .third false ++
  incidenceWords n i names signs .third true

end DFVSGames.Foundations.PCP.RawInitialRows

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RawInitialMachineStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

def clauseInput {n : Nat} (clauses : List (Clause n)) : List Bool :=
  encodeWords (clauses.flatMap Complexity.clauseWords)

@[simp] theorem clauseInput_nil (n : Nat) : clauseInput ([] : List (Clause n)) = [] := rfl

@[simp] theorem clauseInput_cons {n : Nat} (c : Clause n) (cs : List (Clause n)) :
    clauseInput (c :: cs) = encodeWords (Complexity.clauseWords c) ++ clauseInput cs := by
  simp only [clauseInput, List.flatMap_cons, encodeWords_append]

def clauseOutput (n i : Nat) (clauses : List (Clause n)) : List Nat :=
  (clauses.mapIdx fun offset c => RawInitialRows.clauseWords n (i + offset)
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)).flatten

@[simp] theorem clauseOutput_nil (n i : Nat) : clauseOutput n i [] = [] := rfl

@[simp] theorem clauseOutput_cons (n i : Nat) (c : Clause n) (cs : List (Clause n)) :
    clauseOutput n i (c :: cs) =
      RawInitialRows.clauseWords n i (RawInitialRows.clauseNames c)
        (RawInitialRows.clauseSigns c) ++ clauseOutput n (i + 1) cs := by
  simp only [clauseOutput, List.mapIdx_cons, Nat.add_zero, List.flatten_cons,
    Nat.add_comm, Nat.add_left_comm]

end DFVSGames.Foundations.PCP.RawInitialMachineLoopData
end

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

def fieldValue {n : ℕ} (c : Target.Clause n) (j : Fin 6) : ℕ :=
  (Complexity.clauseWords c)[j.val]'(by
    rw [Complexity.clauseWords_length]
    exact j.isLt)

def recordTapes {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .field j => encodeWord (fieldValue c j)
  | k => base k

@[simp] theorem recordTapes_input {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) :
    recordTapes base c suffix .input = suffix := rfl

@[simp] theorem recordTapes_field {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (j : Fin 6) :
    recordTapes base c suffix (.field j) = encodeWord (fieldValue c j) := rfl

@[simp] theorem recordTapes_name {n : ℕ} (base : Tape → List Bool)
    (c : Target.Clause n) (suffix : List Bool) (j : Fin 3) :
    recordTapes base c suffix (.field (nameField j)) =
      encodeWord ((c)[j].variableIndex.val) := by
  fin_cases j <;> rfl

end DFVSGames.Foundations.PCP.RawInitialMachineReadClause

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_RawInitialMachineFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

abbrev Buffer (N : Nat) := MachineFixedBlockMap.Buffer N

namespace Program

open PCP.AlphabetTable

abbrev Ambient := Unit × Buffer 4096
abbrev Plan := List (Emitter.Command 5 Ambient 36864)

end Program

end DFVSGames.Foundations.Complexity.FinalCNFMachine
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFHeader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

def headerResultTapes (n m : Nat) (rowsBits : List Bool) : Tape → List Bool :=
  headerFrame rowsBits (encodeWords [n, m] ++ rowsBits)
    (encodeWord n) (encodeWord m) (encodeWord 0) [] []
    (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse

@[simp] theorem headerResultTapes_input (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .input = rowsBits := rfl

@[simp] theorem headerResultTapes_archive (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .archive = encodeWords [n, m] ++ rowsBits := rfl

@[simp] theorem headerResultTapes_accumulator (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .accumulator =
      (encodeWords [6 * n + 36864 * m, 40960 * m]).reverse := rfl

@[simp] theorem headerResultTapes_rowIndex (n m : Nat) (rowsBits : List Bool) :
    headerResultTapes n m rowsBits .rowIndex = encodeWord 0 := rfl

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable

def endpointTapes (base : Tape → List Bool) (tail reverse : Nat) (rest : List Bool) :=
  Hastad.SourceMachine.fieldTapes Tape.input Tape.reverseIndex
    (Hastad.SourceMachine.fieldTapes Tape.input Tape.tail base
      (encodeWord reverse ++ rest) (encodeWord tail ++ base .tail))
    rest (encodeWord reverse ++ base .reverseIndex)

def finishTapes (base : Tape → List Bool) (row : Nat) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update (Function.update base Tape.tail []) Tape.head [])
      Tape.reverseIndex []) Tape.rowIndex (encodeWord (row + 1))

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFTableAdapter

open PCP

def genericRow {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.DartRow 64 n m :=
  ⟨row.tail, row.reverseIndex, row.relation⟩

@[simp] theorem genericRow_tail {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).tail = row.tail := rfl

@[simp] theorem genericRow_reverseIndex {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).reverseIndex = row.reverseIndex := rfl

@[simp] theorem genericRow_relation {n m : Nat} (row : GraphTables.DartRow n m) :
    (genericRow row).relation = row.relation := rfl

def genericRows {n m : Nat} (rows : GraphTables.Rows n m) :
    GenericGraphTables.Rows 64 n m := rows.map genericRow

@[simp] theorem genericRows_get {n m : Nat} (rows : GraphTables.Rows n m) (e : Fin m) :
    (genericRows rows)[e] = genericRow rows[e] := by
  simp [genericRows]

@[simp] theorem genericRows_reverseAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) :
    GenericGraphTables.reverseAt (genericRows rows) e = GraphTables.reverseAt rows e := by
  change (genericRows rows)[e].reverseIndex = rows[e].reverseIndex
  rw [genericRows_get]
  rfl

@[simp] theorem genericRows_acceptsAt {n m : Nat} (rows : GraphTables.Rows n m)
    (e : Fin m) (a b : Fin 64) :
    GenericGraphTables.acceptsAt (genericRows rows) e a b =
      GraphTables.acceptsAt rows e a b := by
  simp only [GenericGraphTables.acceptsAt, genericRows_get, genericRow_relation]
  rfl

theorem genericRows_valid {n m : Nat} (rows : GraphTables.Rows n m)
    (valid : GraphTables.Valid rows) : GenericGraphTables.Valid (genericRows rows) := by
  constructor
  · intro e
    simpa only [genericRows_reverseAt] using valid.1 e
  · intro e a b
    simpa only [genericRows_reverseAt, genericRows_acceptsAt] using valid.2 e a b

def genericTable (table : GraphTables.Table) : GenericGraphTables.Table 64 where
  vertices := table.vertices
  darts := table.darts
  rows := genericRows table.rows
  valid := genericRows_valid table.rows table.valid

@[simp] theorem genericTable_vertices (table : GraphTables.Table) :
    (genericTable table).vertices = table.vertices := rfl

@[simp] theorem genericTable_darts (table : GraphTables.Table) :
    (genericTable table).darts = table.darts := rfl

@[simp] theorem genericTable_row (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e] = genericRow table.rows[e] := genericRows_get _ _

@[simp] theorem genericTable_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].tail = table.rows[e].tail := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_reverseIndex (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].reverseIndex = table.rows[e].reverseIndex := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericTable_relation (table : GraphTables.Table) (e : Fin table.darts) :
    (genericTable table).rows[e].relation = table.rows[e].relation := by
  rw [genericTable_row]
  rfl

@[simp] theorem genericRow_words {n m : Nat} (row : GraphTables.DartRow n m) :
    GenericGraphTables.rowWords (genericRow row) = GraphTables.rowWords row := rfl

theorem genericTable_rowList (table : GraphTables.Table) :
    GenericGraphTables.rowList (genericTable table) =
      (GraphTables.rowList table).map genericRow := by
  simp only [GenericGraphTables.rowList, GraphTables.rowList, genericTable,
    genericRows, Vector.toList_map]

@[simp] theorem genericTable_tableWords (table : GraphTables.Table) :
    GenericGraphTables.tableWords (genericTable table) = GraphTables.tableWords table := by
  simp only [GenericGraphTables.tableWords, GraphTables.tableWords,
    genericTable_vertices, genericTable_darts, genericTable_rowList, List.flatMap_map,
    genericRow_words]

@[simp] theorem genericTable_tableBits (table : GraphTables.Table) :
    GenericGraphTables.tableBits (genericTable table) = GraphTables.tableBits table := by
  simp only [GenericGraphTables.tableBits, GraphTables.tableBits, genericTable_tableWords]

@[simp] theorem genericTable_semantics_tail (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).tail e =
      (GraphTables.semantics table).tail e := genericTable_tail table e

@[simp] theorem genericTable_semantics_reverse (table : GraphTables.Table)
    (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).reverse e =
      (GraphTables.semantics table).reverse e := genericTable_reverseIndex table e

@[simp] theorem genericTable_semantics_head (table : GraphTables.Table) (e : Fin table.darts) :
    (GenericGraphTables.semantics (genericTable table)).head e =
      (GraphTables.semantics table).head e := by
  simp only [ConstraintGraph.head, genericTable_semantics_reverse, genericTable_semantics_tail]
  rfl

@[simp] theorem genericTable_semantics_accepts (table : GraphTables.Table)
    (e : Fin table.darts) (a b : Fin 64) :
    (GenericGraphTables.semantics (genericTable table)).accepts e a b =
      (GraphTables.semantics table).accepts e a b := genericRows_acceptsAt _ _ _ _

@[simp] theorem genericTable_headIndex (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headIndex (genericTable table) e = table.rows[e].reverseIndex :=
  genericTable_reverseIndex table e

@[simp] theorem genericTable_headValue (table : GraphTables.Table) (e : Fin table.darts) :
    AlphabetTable.Lookup.headValue (genericTable table) e =
      ((GraphTables.semantics table).head e).val := by
  exact (AlphabetTable.Lookup.headValue_eq_semantics (genericTable table) e).trans
    (congrArg Fin.val (genericTable_semantics_head table e))

end DFVSGames.Foundations.Complexity.FinalCNFTableAdapter
end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing PCP PCP.AlphabetTable FinalCNFTableAdapter

@[simp] theorem headRoles_zero : headRoles 0 = Tape.archive := rfl
@[simp] theorem headRoles_one : headRoles 1 = Tape.reverseIndex := rfl
@[simp] theorem headRoles_two : headRoles 2 = Tape.scanWork := rfl
@[simp] theorem headRoles_three : headRoles 3 = Tape.indexWork := rfl
@[simp] theorem headRoles_four : headRoles 4 = Tape.head := rfl
@[simp] theorem headRoles_five : headRoles 5 = Tape.scratch := rfl

def rowOperands (table : GraphTables.Table) (e : Fin table.darts) : Fin 5 → Nat :=
  values table.vertices table.darts table.rows[e].tail.val
    table.rows[table.rows[e].reverseIndex].tail.val e.val

def rowRelation (table : GraphTables.Table) (e : Fin table.darts) : Ambient :=
  ((), fun i => table.rows[e].relation[i])

def rowRest (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) : List Bool :=
  encodeWords (GraphTables.relationWords table.rows[e].relation) ++ rest

def preparedTapes (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headRoles
    (endpointTapes base table.rows[e].tail.val table.rows[e].reverseIndex.val
      (rowRest table e rest)) (genericTable table) e

def emittedTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  Function.update (Function.update (preparedTapes base table e rest) Tape.input rest)
    Tape.accumulator ((plan.flatMap (Emitter.commandBits (rowOperands table e)
      (rowRelation table e))).reverse ++ base .accumulator)

def rowResultTapes (plan : Plan) (base : Tape → List Bool) (table : GraphTables.Table)
    (e : Fin table.darts) (rest : List Bool) : Tape → List Bool :=
  finishTapes (emittedTapes plan base table e rest) e.val

@[simp] theorem rowResult_input (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .input = rest := by
  simp [rowResultTapes, finishTapes, emittedTapes]

@[simp] theorem rowResult_tail (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .tail = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_head (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .head = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_reverse (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .reverseIndex = [] := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_index (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .rowIndex = encodeWord (e.val + 1) := by
  simp [rowResultTapes, finishTapes]

@[simp] theorem rowResult_accumulator (plan : Plan) (base : Tape → List Bool)
    (table : GraphTables.Table) (e : Fin table.darts) (rest : List Bool) :
    rowResultTapes plan base table e rest .accumulator =
      (plan.flatMap (Emitter.commandBits (rowOperands table e) (rowRelation table e))).reverse ++
        base .accumulator := by
  simp [rowResultTapes, finishTapes, emittedTapes]

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_FinalCNFStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP PCP.AlphabetTable FinalCNFTableAdapter

def remainingEvents (table : GraphTables.Table) (r : Nat) : List (Fin table.darts) :=
  (List.finRange table.darts).drop r

def inputStream (table : GraphTables.Table) (events : List (Fin table.darts)) : List Bool :=
  events.flatMap (fun e => encodeWords (GraphTables.rowWords table.rows[e]))

@[simp] theorem remainingEvents_zero (table : GraphTables.Table) :
    remainingEvents table 0 = List.finRange table.darts := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_length (table : GraphTables.Table) (r : Nat) :
    (remainingEvents table r).length = table.darts - r := by
  simp [remainingEvents]

@[simp] theorem remainingEvents_done (table : GraphTables.Table) :
    remainingEvents table table.darts = [] := by
  simp [remainingEvents]

@[simp] theorem inputStream_nil (table : GraphTables.Table) : inputStream table [] = [] := rfl

@[simp] theorem inputStream_cons (table : GraphTables.Table) (e : Fin table.darts)
    (events : List (Fin table.darts)) :
    inputStream table (e :: events) =
      encodeWords (GraphTables.rowWords table.rows[e]) ++ inputStream table events := rfl

end DFVSGames.Foundations.Complexity.FinalCNFMachine.Program

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineLoop

open Turing

def scanTapes (B remaining processed : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord remaining ++ suffix
  | .counter => encodeWord processed
  | .vertices => encodeWord processed
  | .darts => encodeWord (B * processed)

def finalTapes (B n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => suffix
  | .counter => encodeWord n
  | .vertices => encodeWord n
  | .darts => encodeWord (B * n)

end DFVSGames.Foundations.Complexity.PoweringMachineLoop
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMasterState

open Turing
open MachineFixedBlockMap

abbrev OtherRegisters (N : Nat) := Buffer N × (Bool × Option Bool)
abbrev Master (N : Nat) := OtherRegisters N × Option Bool
abbrev CompareState (N : Nat) := Buffer N × (Bool × (Option Bool × Option Bool))
abbrev RowState (N : Nat) := (Bool × (Option Bool × Option Bool)) × Buffer N

def compareEquiv (N : Nat) : Master N ≃ CompareState N :=
  (MachineUnaryEqualityBit.compareStateEquiv (Buffer N)).symm

def rowEquiv (N : Nat) : Master N ≃ RowState N where
  toFun state := ((state.1.2.1, (state.1.2.2, state.2)), state.1.1)
  invFun state := ((state.2, (state.1.1, state.1.2.1)), state.1.2.2)
  left_inv := by rintro ⟨⟨buffer, ⟨flag, left⟩⟩, right⟩; rfl
  right_inv := by rintro ⟨⟨flag, ⟨left, right⟩⟩, buffer⟩; rfl

@[simp] theorem compareEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    compareEquiv N ((buffer, (flag, left)), right) = (buffer, (flag, (left, right))) := rfl

@[simp] theorem compareEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (compareEquiv N).symm (buffer, (flag, (left, right))) = ((buffer, (flag, left)), right) := rfl

@[simp] theorem rowEquiv_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    rowEquiv N ((buffer, (flag, left)), right) = ((flag, (left, right)), buffer) := rfl

@[simp] theorem rowEquiv_symm_apply (N : Nat) (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    (rowEquiv N).symm ((flag, (left, right)), buffer) = ((buffer, (flag, left)), right) := rfl

def withBuffer {N : Nat} (buffer : Buffer N) : Master N :=
  ((buffer, (false, none)), none)

def clean (N : Nat) : Master N := withBuffer (emptyBuffer N)

@[simp] theorem equalityBit_clean {N : Nat} (buffer : Buffer N) :
    MachineUnaryEqualityBit.clean buffer = withBuffer buffer := rfl

@[simp] theorem rowEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    rowEquiv N (withBuffer buffer) = ((false, (none, none)), buffer) := rfl

@[simp] theorem compareEquiv_withBuffer {N : Nat} (buffer : Buffer N) :
    compareEquiv N (withBuffer buffer) = (buffer, (false, (none, none))) := rfl

def clearBuffer {N : Nat} (state : Master N) : Master N :=
  (rowEquiv N).symm ((rowEquiv N state).1, emptyBuffer N)

@[simp] theorem clearBuffer_apply {N : Nat} (buffer : Buffer N)
    (flag : Bool) (left right : Option Bool) :
    clearBuffer ((buffer, (flag, left)), right) =
      ((emptyBuffer N, (flag, left)), right) := rfl

@[simp] theorem clearBuffer_withBuffer {N : Nat} (buffer : Buffer N) :
    clearBuffer (withBuffer buffer) = clean N := rfl

section Row

variable {K Λ : Type} [DecidableEq K] {N M : Nat}

def encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master N) :=
  MachineStateEquiv.statement (rowEquiv N).symm
    (PoweringMachineRow.encodedBlockAt src dst F exit)

def rowAt {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Master (PoweringMachineRow.inputSize t S)) :=
  encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit

end Row

end DFVSGames.Foundations.Complexity.PoweringMasterState
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

inductive Label
  | reverse (l : MachineAffineLookup.Label)
  | endpoint (l : MachineAffineLookup.Label)
  deriving DecidableEq, Fintype

def instruction (tape : Fin 7 → K) (degree port : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .reverse l => MachineAffineLookup.instruction (tape 1) (reverseTapes tape)
      (4098 * degree) (4098 * port + 3) (fun q => labels (.reverse q))
      (some (labels (.endpoint .seed))) l
  | .endpoint l => MachineAffineLookup.instruction (tape 4) (endpointTapes tape)
      4098 2 (fun q => labels (.endpoint q)) exit l

end DFVSGames.Foundations.Complexity.PoweringMachineRotor
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineWord
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def Label : Nat → Type
  | 0 => MachineUnaryAffineAt.Label
  | t + 1 => PoweringMachineRotor.Label ⊕ Label t

instance labelFintype (t : Nat) : Fintype (Label t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype MachineUnaryAffineAt.Label)
  | succ t ih =>
      letI := ih
      exact inferInstanceAs (Fintype (PoweringMachineRotor.Label ⊕ Label t))

def entry : (t : Nat) → Label t
  | 0 => .seed
  | _ + 1 => .inl (.reverse .seed)

def copyInstruction (source scratch output : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output 0 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch output 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

def instruction : (t : Nat) → (Tape t → K) → (Fin t → Fin d) →
    (Label t → Λ) → Option Λ → Label t →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, placement, _, labels, exit =>
      copyInstruction (placement (.inr (first 0))) (placement (.inl 4))
        (placement (.inl 5)) labels exit
  | t + 1, placement, ports, labels, exit => fun l =>
      match l with
      | .inl q => PoweringMachineRotor.instruction (placement ∘ rotorRole t) d (ports 0).val
          (fun z => labels (.inl z)) (some (labels (.inr (entry t)))) q
      | .inr q => instruction t (placement ∘ shift t) (fun j => ports j.succ)
          (fun z => labels (.inr z)) exit q

end DFVSGames.Foundations.Complexity.PoweringMachineWord
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop PoweringMasterState

def dropUnit_inline_PoweringMachineInitialize (N : Nat) : (Master N × Unit) ≃ Master N where
  toFun := Prod.fst
  invFun state := (state, ())
  left_inv := by rintro ⟨state, ⟨⟩⟩; rfl
  right_inv := by intro state; rfl

def headerStatement (max N B : Nat) (label : HeaderLabel) :
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N) :=
  MachineStateEquiv.statement (dropUnit_inline_PoweringMachineInitialize N)
    (castStatement_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max)
      (MachineEmbedding.statement (Λextra := MachineUnaryAffineAt.Label)
        (τ := Unit) none (headerProgram (σ := OtherRegisters N) B label)))

def program (max N B : Nat) : Label →
    TM2.Stmt (fun _ : GlobalTape max => Bool) Label (Master N)
  | .inl label => headerStatement max N B label
  | .inr .seed => MachineUnaryAffineAt.seed (.inl .source) 0 (.inr .scan)
  | .inr .scan => MachineUnaryAffineAt.scan
      (commonPlacement max (PoweringMachineTapes.table max))
      (commonPlacement max (PoweringMachineTapes.scratch max))
      (.inl .source) 1 (.inr .scan) (.inr .restore)
  | .inr .restore => Reduction.MachineTransfer.loopAt
      (commonPlacement max (PoweringMachineTapes.scratch max))
      (commonPlacement max (PoweringMachineTapes.table max))
      id false (.inr .restore) (some (.inl .initialize_))

def instruction {Λ : Type} (max N B : Nat) (labels : Label → Λ) (exit : Option Λ)
    (label : Label) : TM2.Stmt (fun _ : GlobalTape max => Bool) Λ (Master N) :=
  MachineSubroutine.statement labels exit (program max N B label)

@[simp] theorem final_counter (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra
      (commonPlacement max (PoweringMachineTapes.start max)) = encodeWord vertices := by
  simp [mergeTapes, finalTapes]

@[simp] theorem final_vertices (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .vertices) = encodeWord vertices := rfl

@[simp] theorem final_darts (max B vertices : Nat) (extra : ExtraTape max → List Bool) :
    mergeTapes (finalTapes B vertices []) extra (.inl .darts) = encodeWord (B * vertices) := rfl

@[simp] theorem final_extra (max B vertices : Nat) (extra : ExtraTape max → List Bool)
    (tape : ExtraTape max) :
    mergeTapes (finalTapes B vertices []) extra (.inr tape) = extra tape := rfl

end DFVSGames.Foundations.Complexity.PoweringMachineInitialize
end

section

namespace DFVSGames.Foundations.Complexity.PoweringGlobalEnumeration

open PoweringMachineLoop PoweringMachineInitialize

def headerTapeEquiv : HeaderTape ≃ Fin 4 where
  toFun
    | .source => 0
    | .counter => 1
    | .vertices => 2
    | .darts => 3
  invFun i := if i = 0 then .source else if i = 1 then .counter
    else if i = 2 then .vertices else .darts
  left_inv tape := by cases tape <;> rfl
  right_inv i := by fin_cases i <;> rfl

def extraTapeEquiv (max : Nat) : ExtraTape max ≃ Fin (11 + max + 1) :=
  (Equiv.sumCongr (sharedTapeEquiv max) unitTapeEquiv).trans finSumFinEquiv

def globalTapeEquiv (max : Nat) : GlobalTape max ≃ Fin (4 + (11 + max + 1)) :=
  (Equiv.sumCongr headerTapeEquiv (extraTapeEquiv max)).trans finSumFinEquiv

def enumeration (max : Nat) : Fin (4 + (11 + max + 1)) ≃ GlobalTape max :=
  (globalTapeEquiv max).symm

@[simp] theorem globalTapeEquiv_enumeration (max : Nat) (i : Fin (4 + (11 + max + 1))) :
    globalTapeEquiv max (enumeration max i) = i :=
  (globalTapeEquiv max).apply_symm_apply i

@[simp] theorem enumeration_globalTapeEquiv (max : Nat) (tape : GlobalTape max) :
    enumeration max (globalTapeEquiv max tape) = tape :=
  (globalTapeEquiv max).symm_apply_apply tape

@[simp] theorem source_index (max : Nat) :
    (globalTapeEquiv max (.inl .source)).val = 0 := rfl

@[simp] theorem counter_index (max : Nat) :
    (globalTapeEquiv max (.inl .counter)).val = 1 := rfl

@[simp] theorem vertices_index (max : Nat) :
    (globalTapeEquiv max (.inl .vertices)).val = 2 := rfl

@[simp] theorem darts_index (max : Nat) :
    (globalTapeEquiv max (.inl .darts)).val = 3 := rfl

@[simp] theorem finalOutput_index (max : Nat) :
    (globalTapeEquiv max (finalOutput max)).val = 4 + (11 + max) := rfl

end DFVSGames.Foundations.Complexity.PoweringGlobalEnumeration
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def instruction (source : K) (tape : Fin 5 → K) (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ) :
    MachineAffineLookup.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineAffineLookup.instruction source tape (4098 * d)
    (4098 * port.val + 4 + position.val) labels exit

end DFVSGames.Foundations.Complexity.PoweringMachineRelation
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineRelationField
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

abbrev State (A : Type) := MachineUnaryEqualityBit.State A
abbrev Label (path : List (Fin d)) := PoweringMachineWord.Label path.length ⊕ MachineAffineLookup.Label

def instruction (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ) :
    Label path → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
      path.get (fun z => labels (.inl z)) (some (labels (.inr .seed))) q
  | .inr q => PoweringMachineRelation.instruction (placement (.inl 6)) (lookupTapes placement)
      port (GraphTables.relationIndex (left, right)) (fun z => labels (.inr z)) exit q

end DFVSGames.Foundations.Complexity.PoweringMachineRelationField
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

abbrev State := MachineUnaryEqualityBit.State
abbrev Label (l r : Nat) :=
  PoweringMachineWord.Label l ⊕ PoweringMachineWord.Label r ⊕ MachineUnaryEqualityBit.Label

def entry (l r : Nat) : Label l r := .inl (PoweringMachineWord.entry l)

def instruction (hl : l ≤ max) (hr : r ≤ max) (placement : Tape max → K)
    (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ) :
    Label l r → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction l
      (placement ∘ PoweringMachineTapes.wordPlacement hl false) left
      (fun z => labels (.inl z))
      (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) q
  | .inr (.inl q) => PoweringMachineWord.instruction r
      (placement ∘ PoweringMachineTapes.wordPlacement hr true) right
      (fun z => labels (.inr (.inl z)))
      (some (labels (.inr (.inr .seedLeft)))) q
  | .inr (.inr q) => MachineUnaryEqualityBit.instruction
      (placement ∘ PoweringMachineTapes.equalityPlacement max)
      (fun z => labels (.inr (.inr z))) exit q

end DFVSGames.Foundations.Complexity.PoweringMachineEqualityField
end

section

namespace DFVSGames.Foundations.PCP.PoweringRowData

open DFVSGames.Foundations.Complexity
open Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

def endpointMask (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center target : Fin vertices) (i : AddressIndex d t) : Bool :=
  decide ((wordToBall G t center ((allAddresses d t).get i)).val = target)

def slotCount (d n : Nat) : Nat := (allAddresses d (n + 1)).length

abbrev RowBuffer (d n : Nat) := Buffer (inputSize (n + 1) (slotCount d n))

def fixedLabelAt (d n : Nat) (a : Fin (PoweringTables.labelCount d n))
    (i : Fin (slotCount d n)) : GraphTables.Label :=
  decodeLabel d (n + 1) 64 a ((allAddresses d (n + 1)).get i)

def walkData (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1))
    (k : Fin (n + 1)) : Field (slotCount d n) → Bool
  | .inl (a, b) => PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k) a b
  | .inr (.inl i) => endpointMask (PortTables.portGraph input) (n + 1) w.1
      (edgeAt (PortTables.portGraph input) n w k).1 i
  | .inr (.inr i) => endpointMask (PortTables.portGraph input) (n + 1)
      (endpoint (PortTables.portGraph input) w)
      ((PortTables.portGraph input).rot (edgeAt (PortTables.portGraph input) n w k)).1 i

def walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : RowBuffer d n :=
  packData (walkData input n w)

@[simp] theorem basePredicate_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a b : GraphTables.Label) :
    basePredicate (walkBits input n w) k a b =
      PortTables.accepts input (edgeAt (PortTables.portGraph input) n w k) a b := by
  simp [basePredicate, walkBits, walkData]

@[simp] theorem leftMatches_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    leftMatches (walkBits input n w) k = endpointMask (PortTables.portGraph input)
      (n + 1) w.1 (edgeAt (PortTables.portGraph input) n w k).1 := by
  funext i
  simp [leftMatches, walkBits, walkData]

@[simp] theorem rightMatches_walkBits (input : PortTables.Table vertices d) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    rightMatches (walkBits input n w) k = endpointMask (PortTables.portGraph input)
      (n + 1) (endpoint (PortTables.portGraph input) w)
      ((PortTables.portGraph input).rot (edgeAt (PortTables.portGraph input) n w k)).1 := by
  funext i
  simp [rightMatches, walkBits, walkData]

def transposeField {S : Nat} : Field S → Field S
  | .inl (a, b) => .inl (b, a)
  | .inr (.inl i) => .inr (.inr i)
  | .inr (.inr i) => .inr (.inl i)

def transposeBits {t S : Nat} (bits : Buffer (inputSize t S)) : Buffer (inputSize t S) :=
  packData fun k field => bits (inputEquiv t S (k, transposeField field))

@[simp] theorem basePredicate_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) (a b : GraphTables.Label) :
    basePredicate (transposeBits bits) k a b = basePredicate bits k b a := by
  simp [basePredicate, transposeBits, transposeField]

@[simp] theorem leftMatches_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) :
    leftMatches (transposeBits bits) k = rightMatches bits k := by
  funext i
  simp [leftMatches, rightMatches, transposeBits, transposeField]

@[simp] theorem rightMatches_transposeBits {t S : Nat}
    (bits : Buffer (inputSize t S)) (k : Fin t) :
    rightMatches (transposeBits bits) k = leftMatches bits k := by
  funext i
  simp [leftMatches, rightMatches, transposeBits, transposeField]

def rowBits (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) : RowBuffer d n :=
  if e.1 then transposeBits (walkBits input n e.2) else walkBits input n e.2

def rowData (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) : Bool :=
  walkData input n e.2 k (if e.1 then transposeField field else field)

theorem rowBits_packData (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    rowBits input n e = packData (rowData input n e) := by
  rcases e with ⟨direction, w⟩
  cases direction <;> funext i <;>
    simp [rowBits, rowData, transposeBits, walkBits, packData]

@[simp] theorem rowBits_field (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    rowBits input n e (inputEquiv (n + 1) (slotCount d n) (k, field)) =
      rowData input n e k field := by
  rw [rowBits_packData, packData_inputEquiv]

end DFVSGames.Foundations.PCP.PoweringRowData
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Probability_PoweringFieldPlan
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open DFVSGames.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

def addressPorts {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) : List (Fin d) :=
  List.ofFn ((allAddresses d t).get i).2

theorem addressPorts_length_le {d t : Nat} (i : PoweringOpinionTables.AddressIndex d t) :
    (addressPorts i).length ≤ t := by
  simp only [addressPorts, List.length_ofFn]
  exact Nat.le_of_lt_succ ((allAddresses d t).get i).1.isLt

def fieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) : Field (slotCount d n) → Instruction d
  | .inl (a, b) => .relation (tailPorts n ports k) (ports k) a b
  | .inr (.inl i) => .equal (addressPorts i) (tailPorts n ports k)
  | .inr (.inr i) => .equal (List.ofFn ports ++ addressPorts i) (headPorts n ports k)

def directedFieldPlan {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) : Instruction d :=
  fieldPlan n ports k (if direction then transposeField field else field)

theorem fieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (fieldPlan n ports k field).radius ≤ 2 * (n + 1) := by
  have hk := k.isLt
  rcases field with ⟨a,b⟩ | i | i
  · simp only [fieldPlan, Instruction.radius, tailPorts_length]
    omega
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, tailPorts_length]
    exact max_le (by omega) (by omega)
  · have hi := addressPorts_length_le i
    simp only [fieldPlan, Instruction.radius, headPorts, List.length_append,
      List.length_ofFn, List.length_singleton, tailPorts_length]
    exact max_le (by omega) (by omega)

theorem directedFieldPlan_radius {d : Nat} (n : Nat) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (k : Fin (n + 1)) (field : Field (slotCount d n)) :
    (directedFieldPlan n ports direction k field).radius ≤ 2 * (n + 1) :=
  fieldPlan_radius n ports k _

end DFVSGames.Foundations.PCP.PoweringFieldPlan
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

abbrev State := MachineUnaryEqualityBit.State

def Label : Instruction d → Type
  | .relation path _ _ _ => PoweringMachineRelationField.Label path
  | .equal left right => PoweringMachineEqualityField.Label left.length right.length

instance labelFintype (op : Instruction d) : Fintype (Label op) := by
  cases op <;> dsimp only [Label] <;> infer_instance

def entry : (op : Instruction d) → Label op
  | .relation path _ _ _ => .inl (PoweringMachineWord.entry path.length)
  | .equal left right => PoweringMachineEqualityField.entry left.length right.length

def instruction (placement : Tape max → K) : (op : Instruction d) → op.radius ≤ max →
    (Label op → Λ) → Option Λ → Label op → TM2.Stmt (fun _ : K => Bool) Λ (State A)
  | .relation path port a b, bounded, labels, exit =>
      PoweringMachineRelationField.instruction placement path bounded port a b labels exit
  | .equal left right, bounded, labels, exit =>
      PoweringMachineEqualityField.instruction
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement left.get right.get labels exit

end DFVSGames.Foundations.Complexity.PoweringMachineField
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

abbrev LocalLabel (op : Command d max) := PoweringMachineField.Label op.val
abbrev Label (commands : List (Command d max)) := MachineFiniteSequence.Label LocalLabel commands

def instruction (placement : PoweringMachineTapes.Tape max → K)
    (commands : List (Command d max)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A) :=
  MachineFiniteSequence.instruction LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    commands labels exit

def boundedRowPlan (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    List (Command d (2 * (n + 1))) :=
  List.ofFn fun i : Fin (PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n)) =>
    let pair := (PoweringMachineRow.inputEquiv (n + 1) (PoweringRowData.slotCount d n)).symm i
    ⟨directedFieldPlan n ports direction pair.1 pair.2,
      directedFieldPlan_radius n ports direction pair.1 pair.2⟩

end DFVSGames.Foundations.Complexity.PoweringMachinePlan
end

section

namespace DFVSGames.Foundations.Complexity.PoweringPlanBudget

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

@[simp] theorem boundedRowPlan_length (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    (PoweringMachinePlan.boundedRowPlan n ports direction).length =
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) := by
  simp only [PoweringMachinePlan.boundedRowPlan, List.length_ofFn]

end DFVSGames.Foundations.Complexity.PoweringPlanBudget
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

@[simp] theorem headerPlacement_start {t max : Nat} (h : t ≤ max) :
    headerPlacement h (.inr (PoweringMachineWord.first t)) = start max := by
  simp [headerPlacement, start, leftEndpoint, rowOutput, Equiv.swap_apply_def]

@[simp] theorem headerPlacement_succ {t max : Nat} (h : t ≤ max) (i : Fin t) :
    headerPlacement h (.inr i.succ) = .inr (Fin.castLE h i) := by
  simp [headerPlacement, leftEndpoint, rowOutput, Equiv.swap_apply_def]

abbrev Label (n : Nat) := MachineUnaryAffineAt.Label ⊕
  (MachineUnaryAffineAt.Label ⊕ PoweringMachineWord.Label (n + 1))

def entry (n : Nat) : Label n := .inl .seed

def tailEntry (n : Nat) (direction : Bool) : Label n :=
  if direction then .inr (.inr (PoweringMachineWord.entry (n + 1))) else .inr (.inl .seed)

def affineInstruction (source work output : K) (coefficient offset : Nat)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output offset (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source work output coefficient (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt work source id false (labels .restore) exit

def instruction (n : Nat) (h : n + 1 ≤ max) (placement : Tape max → K)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ) :
    Label n → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl q => affineInstruction (placement (start max)) (placement (scratch max))
      (placement (rowOutput max)) (blockSize d n) (reverseOffset d n ports direction)
      (fun z => labels (.inl z)) (some (labels (tailEntry n direction))) q
  | .inr (.inl q) => PoweringMachineWord.copyInstruction
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (fun z => labels (.inr (.inl z))) exit q
  | .inr (.inr q) => PoweringMachineWord.instruction (n + 1)
      (placement ∘ headerPlacement h) ports (fun z => labels (.inr (.inr z))) exit q

end DFVSGames.Foundations.Complexity.PoweringMachineRowHeaders
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineRowBody
attribute [-instance] _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev bufferSize (d n : Nat) := PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n)
abbrev State (d n : Nat) := PoweringMasterState.Master (bufferSize d n)

def commands (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :=
  (PoweringMachinePlan.boundedRowPlan n ports direction).reverse

abbrev Label (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :=
  PoweringMachinePlan.Label (commands n ports direction) ⊕
    (Unit ⊕ PoweringMachineRowHeaders.Label n)

def planMain {max : Nat} {E : Type}
    (ops : List (PoweringMachinePlan.Command d max)) (fallback : E) :
    PoweringMachinePlan.Label ops ⊕ E :=
  match ops with
  | [] => .inr fallback
  | op :: _ => .inl (.inl (PoweringMachineField.entry op.val))

def entry (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Label n ports direction :=
  planMain (commands n ports direction) (.inl ())

def headerPlacement {max : Nat} (placement : PoweringMachineTapes.Tape max → K)
    (output : K) (i : PoweringMachineTapes.Tape max) : K :=
  if i = .inl 10 then output else placement i

omit [DecidableEq K] in
@[simp] theorem headerPlacement_output {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (output : K) :
    headerPlacement placement output (.inl 10) = output := by simp [headerPlacement]

def instruction (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K)
    (output : K) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ) :
    Label n ports direction → TM2.Stmt (fun _ : K => Bool) Λ (State d n)
  | .inl q => PoweringMachinePlan.instruction placement (commands n ports direction)
      (fun z => labels (.inl z)) (some (labels (.inr (.inl ())))) q
  | .inr (.inl _) => PoweringMasterState.rowAt (t := n + 1) (placement (.inl 10)) output
      (PoweringRowData.fixedLabelAt d n) (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n)))))
  | .inr (.inr q) => PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction (fun z => labels (.inr (.inr z))) exit q

end DFVSGames.Foundations.Complexity.PoweringMachineRowBody
end

section

namespace DFVSGames.Foundations.PCP.PoweringTableLayout

open DFVSGames.Foundations.Complexity
open PoweringTables PoweringEnumeration

theorem dartCount_eq_vertex_blocks (vertices d n : Nat) :
    dartCount vertices d n = vertices * blockSize d n := by
  unfold dartCount blockSize
  ac_rfl

def blockIndex {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) : Fin (dartCount vertices d n) :=
  Fin.cast (dartCount_eq_vertex_blocks vertices d n).symm
    (finProdFinEquiv (v, j))

@[simp] theorem blockIndex_val {vertices : Nat} (d n : Nat) (v : Fin vertices)
    (j : Fin (blockSize d n)) :
    (blockIndex d n v j).val = blockSize d n * v.val + j.val := by
  change j.val + blockSize d n * v.val = blockSize d n * v.val + j.val
  exact Nat.add_comm _ _

def vertexRows {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat)
    (v : Fin vertices) :
    List (GenericGraphTables.DartRow (labelCount d n) vertices (dartCount vertices d n)) :=
  List.ofFn (fun j : Fin (blockSize d n) => (table input n).rows[blockIndex d n v j])

@[simp] theorem vertexRows_length {vertices d : Nat}
    (input : PortTables.Table vertices d) (n : Nat) (v : Fin vertices) :
    (vertexRows input n v).length = blockSize d n := by
  exact List.length_ofFn (f := fun j : Fin (blockSize d n) =>
    (table input n).rows[blockIndex d n v j])

end DFVSGames.Foundations.PCP.PoweringTableLayout
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev Command (d n : Nat) := Fin (PoweringTableLayout.blockSize d n)

def ports {d n : Nat} (j : Command d n) : Fin (n + 1) → Fin d :=
  ((PoweringEnumeration.dartBlockEquiv d n).symm j).1

def direction {d n : Nat} (j : Command d n) : Bool :=
  ((PoweringEnumeration.dartBlockEquiv d n).symm j).2

def commands (d n : Nat) : List (Command d n) := (List.ofFn id).reverse

@[simp] theorem commands_length (d n : Nat) :
    (commands d n).length = PoweringTableLayout.blockSize d n := by
  simp only [commands, List.length_reverse, List.length_ofFn]

abbrev LocalLabel (j : Command d n) := PoweringMachineRowBody.Label n (ports j) (direction j)
abbrev SequenceLabel (ops : List (Command d n)) := MachineFiniteSequence.Label LocalLabel ops
abbrev Label (d n : Nat) := SequenceLabel (commands d n)
abbrev State (d n : Nat) := PoweringMachineRowBody.State d n

def sequenceEntry (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : Option Λ :=
  MachineFiniteSequence.entry LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j)) ops labels exit

def entry (d n : Nat) (labels : Label d n → Λ) (exit : Option Λ) : Option Λ :=
  sequenceEntry (commands d n) labels exit

def sequenceInstruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : SequenceLabel ops → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  MachineFiniteSequence.instruction LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    ops labels exit

def instruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (labels : Label d n → Λ) (exit : Option Λ) :
    Label d n → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  sequenceInstruction n placement output (commands d n) labels exit

end DFVSGames.Foundations.Complexity.PoweringMachineVertex
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_PoweringMachineOuterLoop
attribute [-instance] _root_.OAI.DFVSGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.DFVSGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

abbrev State := PoweringMachineVertex.State

def vertexStart (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) : Λ :=
  (PoweringMachineVertex.entry d n labels (some guardLabel)).getD guardLabel

def bridge (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  .goto (fun _ => vertexStart d n labels guardLabel)

end DFVSGames.Foundations.Complexity.PoweringMachineOuterLoop
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

def copyInstruction (source scratch output : K)
    (labels : MachineUnaryAffineAt.Label → Λ) (exit : Option Λ) :
    MachineUnaryAffineAt.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .seed => MachineUnaryAffineAt.seed output 0 (labels .scan)
  | .scan => MachineUnaryAffineAt.scan source scratch output 1 (labels .scan) (labels .restore)
  | .restore => Reduction.MachineTransfer.loopAt scratch source id false (labels .restore) exit

def instruction (enumeration : Fin N ≃ K) (headerV headerD output scratch : K)
    (labels : Label enumeration output → Λ) :
    Label enumeration output → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .inl l => copyInstruction headerD scratch output (fun q => labels (.inl q))
      (some (labels (.inr (.inl .seed)))) l
  | .inr (.inl l) => copyInstruction headerV scratch output
      (fun q => labels (.inr (.inl q)))
      (MachineDrainMany.entry (MachineDrainMany.workTapes enumeration output)
        (fun q => labels (.inr (.inr q))) none) l
  | .inr (.inr l) => MachineDrainMany.instruction
      (MachineDrainMany.workTapes enumeration output) (fun q => labels (.inr (.inr q))) none l

def afterHeaders (output : K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update base output (encodeWords [n, m] ++ base output)

@[simp] theorem afterHeaders_output (output : K) (base : K → List Bool) (n m : Nat) :
    afterHeaders output base n m output = encodeWords [n, m] ++ base output := by
  simp only [afterHeaders, Function.update_self]

end DFVSGames.Foundations.Complexity.PoweringMachineFinish
end

section

namespace DFVSGames.Foundations.Complexity.PoweringMachineGlobal

open Turing

abbrev Tape (n : Nat) :=
  PoweringMachineInitialize.GlobalTape (PoweringMachineRowBody.capacity n)

abbrev State (d n : Nat) :=
  PoweringMasterState.Master (PoweringMachineRowBody.bufferSize d n)

def placement (n : Nat) :
    PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → Tape n :=
  PoweringMachineInitialize.commonPlacement (PoweringMachineRowBody.capacity n)

def inputTape (n : Nat) : Tape n :=
  placement n (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

def outputTape (n : Nat) : Tape n :=
  PoweringMachineInitialize.finalOutput (PoweringMachineRowBody.capacity n)

def headerVertices (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.vertices
def headerDarts (n : Nat) : Tape n := .inl PoweringMachineLoop.HeaderTape.darts

def enumeration (n : Nat) :
    Fin (4 + (11 + PoweringMachineRowBody.capacity n + 1)) ≃ Tape n :=
  PoweringGlobalEnumeration.enumeration (PoweringMachineRowBody.capacity n)

abbrev FinishLabel (n : Nat) := PoweringMachineFinish.Label (enumeration n) (outputTape n)

abbrev Label (d n : Nat) := PoweringMachineInitialize.Label ⊕
  (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))

instance labelFintype (d n : Nat) : Fintype (Label d n) :=
  inferInstanceAs (Fintype (PoweringMachineInitialize.Label ⊕
    (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))))

def initLabels (d n : Nat) : PoweringMachineInitialize.Label → Label d n := Sum.inl
def guardLabel (d n : Nat) : Label d n := .inr (.inl false)
def bridgeLabel (d n : Nat) : Label d n := .inr (.inl true)

def vertexLabels (d n : Nat) (label : PoweringMachineVertex.Label d n) : Label d n :=
  .inr (.inr (.inl label))

def finishLabels (d n : Nat) (label : FinishLabel n) : Label d n :=
  .inr (.inr (.inr label))

def finishEntry (d n : Nat) : Label d n := finishLabels d n (.inl .seed)

def main (d n : Nat) : Label d n := initLabels d n (.inr .seed)

def program (d n : Nat) :
    Label d n → TM2.Stmt (fun _ : Tape n => Bool) (Label d n) (State d n)
  | .inl label => PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label
  | .inr (.inl false) => MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n)
  | .inr (.inl true) => PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n)
  | .inr (.inr (.inl label)) => PoweringMachineVertex.instruction n (placement n) (outputTape n)
      (vertexLabels d n) (some (guardLabel d n)) label
  | .inr (.inr (.inr label)) => PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label

@[simp] theorem atInit (d n : Nat) (label : PoweringMachineInitialize.Label) :
    program d n (initLabels d n label) = PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atGuard (d n : Nat) :
    program d n (guardLabel d n) = MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n) := rfl

@[simp] theorem atBridge (d n : Nat) :
    program d n (bridgeLabel d n) =
      PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n) := rfl

@[simp] theorem atVertex (d n : Nat) (label : PoweringMachineVertex.Label d n) :
    program d n (vertexLabels d n label) = PoweringMachineVertex.instruction n
      (placement n) (outputTape n) (vertexLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atFinish (d n : Nat) (label : FinishLabel n) :
    program d n (finishLabels d n label) = PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label := rfl

def machine (d n : Nat) : FinTM2 where
  K := Tape n
  k₀ := inputTape n
  k₁ := outputTape n
  Γ _ := Bool
  Λ := Label d n
  main := main d n
  σ := State d n
  initialState := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  m := program d n

@[simp] theorem machine_code (d n : Nat) (label : Label d n) :
    (machine d n).m label = program d n label := rfl

@[simp] theorem machine_main (d n : Nat) : (machine d n).main = main d n := rfl

@[simp] theorem machine_initialState (d n : Nat) :
    (machine d n).initialState = PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n) := rfl

end DFVSGames.Foundations.Complexity.PoweringMachineGlobal
end

section

namespace DFVSGames.Foundations.Complexity.PoweringInitializeFrame

open Turing PCP

variable {vertices d : Nat}

def initialExtra (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.ExtraTape (PoweringMachineRowBody.capacity n) → List Bool :=
  fun tape => if tape = .inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))
    then PortTables.tableBits graph else []

@[simp] theorem initialExtra_table (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n (.inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))) =
      PortTables.tableBits graph := by simp [initialExtra]

@[simp] theorem initialExtra_scratch (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n
      (.inl (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n))) = [] := by
  simp [initialExtra, PoweringMachineTapes.table, PoweringMachineTapes.scratch]

def preparedTapes (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineGlobal.Tape n → List Bool :=
  PoweringMachineInitialize.mergeTapes
    (PoweringMachineLoop.finalTapes (PoweringTableLayout.blockSize d n) vertices [])
    (initialExtra graph n)

@[simp] theorem prepared_start (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl 1)) =
      encodeWord vertices := by
  simpa only [preparedTapes, PoweringMachineGlobal.placement, PoweringMachineTapes.start] using
    PoweringMachineInitialize.final_counter (PoweringMachineRowBody.capacity n)
      (PoweringTableLayout.blockSize d n) vertices (initialExtra graph n)

@[simp] theorem prepared_output (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.outputTape n) = [] := by
  simp [preparedTapes, PoweringMachineGlobal.outputTape, PoweringMachineInitialize.finalOutput,
    PoweringMachineInitialize.mergeTapes, initialExtra]

@[simp] theorem prepared_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerVertices n) = encodeWord vertices := rfl

@[simp] theorem prepared_darts (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := rfl

end DFVSGames.Foundations.Complexity.PoweringInitializeFrame
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_Clone100Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Explicit.MachineClone100Model

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad

def affineEmit (scale offset : Nat) : Bool → List Bool
  | true => List.replicate scale true
  | false => encodeWord offset

def emission (triples : List (Nat × Nat × Nat)) (c : Context triples.length) :
    Bool → List Bool := affineEmit (contextScale c) (contextOffset triples c)

end DFVSGames.Explicit.MachineClone100Model
end

section

namespace DFVSGames.Explicit.MachineClone100Context

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

def contextTapes (triples : List (Nat × Nat × Nat)) (context : Context triples.length)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .reversed
    ((MachineTransducer.output (fun control _ => control) (emission triples)
      context (base (contextSource context))).reverse ++ base .reversed)

@[simp] theorem contextTapes_reversed (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .reversed =
      (MachineTransducer.output (fun control _ => control) (emission triples)
        context (base (contextSource context))).reverse ++ base .reversed := by
  simp [contextTapes]

theorem contextTapes_other (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) (tape : Tape)
    (different : tape ≠ .reversed) :
    contextTapes triples context base tape = base tape := by
  simp [contextTapes, different]

@[simp] theorem contextTapes_source (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base (contextSource context) = base (contextSource context) :=
  contextTapes_other triples context base _ (contextSource_ne_reversed context)

@[simp] theorem contextTapes_scratch (triples : List (Nat × Nat × Nat))
    (context : Context triples.length) (base : Tape → List Bool) :
    contextTapes triples context base .scratch = base .scratch :=
  contextTapes_other triples context base _ (by decide)

end DFVSGames.Explicit.MachineClone100Context
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_RankGraph_MachineClone100Cleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Explicit.MachineClone100Cleanup

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open MachineClone100Model

variable {D : Nat}

def clearFields (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (.field 0) []) (.field 1) []) (.field 2) []) (.field 3) []

@[simp] theorem clearFields_field (base : Tape → List Bool) (j : Fin 4) :
    clearFields base (.field j) = [] := by
  fin_cases j <;> simp [clearFields]

@[simp] theorem clearFields_input (base : Tape → List Bool) :
    clearFields base .input = base .input := by simp [clearFields]
@[simp] theorem clearFields_header (base : Tape → List Bool) :
    clearFields base .header = base .header := by simp [clearFields]
@[simp] theorem clearFields_counter (base : Tape → List Bool) :
    clearFields base .counter = base .counter := by simp [clearFields]
@[simp] theorem clearFields_scratch (base : Tape → List Bool) :
    clearFields base .scratch = base .scratch := by simp [clearFields]
@[simp] theorem clearFields_reversed (base : Tape → List Bool) :
    clearFields base .reversed = base .reversed := by simp [clearFields]
@[simp] theorem clearFields_output (base : Tape → List Bool) :
    clearFields base .output = base .output := by simp [clearFields]

end DFVSGames.Explicit.MachineClone100Cleanup
end

section

namespace DFVSGames.Explicit.MachineClone100Headers

open DFVSGames.Reduction

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineClone100Model

def resultTapes (triples : List (Nat × Nat × Nat)) (base : Tape → List Bool)
    (n m : Nat) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .header => []
  | .counter => encodeWord m
  | .reversed => (encodeWords [100 * n, triples.length * m]).reverse
  | tape => base tape

@[simp] theorem resultTapes_input (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .input = suffix := rfl
@[simp] theorem resultTapes_header (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .header = [] := rfl
@[simp] theorem resultTapes_counter (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .counter = encodeWord m := rfl
@[simp] theorem resultTapes_reversed (triples) (base) (n m) (suffix) :
    resultTapes triples base n m suffix .reversed =
      (encodeWords [100 * n, triples.length * m]).reverse := rfl

end DFVSGames.Explicit.MachineClone100Headers
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Explicit.MachineSingleOrbitCodec

open DFVSGames.Foundations.Target DFVSGames.Foundations.Complexity

def rowBits {n q : Nat} (c : Constraint n q) : List Bool :=
  encodeWords (constraintWords c)

def doubledRowBits {n q : Nat} (c : Constraint n q) : List Bool :=
  encodeWords (constraintWords (doubleConstraint c))

def rowsBits {n q : Nat} (cs : List (Constraint n q)) : List Bool :=
  encodeWords (cs.flatMap constraintWords)

def doubledRowsBits {n q : Nat} (cs : List (Constraint n q)) : List Bool :=
  encodeWords (cs.flatMap (fun c => constraintWords (doubleConstraint c)))

@[simp] theorem rowBits_eq {n q : Nat} (c : Constraint n q) :
    rowBits c = encodeWord c.source.val ++ encodeWord c.target.val ++
      encodeWords (tableWords c.permutation) := by
  simp [rowBits, constraintWords, encodeWords, List.append_assoc]

@[simp] theorem doubledRowBits_eq {n q : Nat} (c : Constraint n q) :
    doubledRowBits c = encodeWord c.source.val ++ encodeWord (n + c.target.val) ++
      encodeWords (tableWords c.permutation) := by
  simp [doubledRowBits, constraintWords, doubleConstraint, encodeWords, List.append_assoc]

@[simp] theorem rowsBits_nil {n q : Nat} : rowsBits ([] : List (Constraint n q)) = [] := rfl
@[simp] theorem doubledRowsBits_nil {n q : Nat} :
    doubledRowsBits ([] : List (Constraint n q)) = [] := rfl

@[simp] theorem rowsBits_cons {n q : Nat} (c : Constraint n q) (cs : List (Constraint n q)) :
    rowsBits (c :: cs) = rowBits c ++ rowsBits cs := by
  simp [rowsBits, rowBits]

@[simp] theorem doubledRowsBits_cons {n q : Nat} (c : Constraint n q)
    (cs : List (Constraint n q)) :
    doubledRowsBits (c :: cs) = doubledRowBits c ++ doubledRowsBits cs := by
  simp [doubledRowsBits, doubledRowBits]

end DFVSGames.Explicit.MachineSingleOrbitCodec
end

section

namespace DFVSGames.Reduction.SourceEquationLookup

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition SourceMachine SourceEncoding
variable {σ : Type}

@[simp] theorem scanTapes_work (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) : scanTapes base i indexSuffix input .work = input := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

@[simp] theorem scanTapes_index (base : Tape → List Bool) (i : Nat)
    (indexSuffix input : List Bool) :
    scanTapes base i indexSuffix input .index = encodeWord i ++ indexSuffix := by
  simp [scanTapes, MachineUnaryCounter.counterTapes]

end DFVSGames.Reduction.SourceEquationLookup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineSourceTuple

open Turing DFVSGames.Foundations.Complexity
open SourceEncoding
open MachineComposition

variable {width : Nat} {Extra σ : Type}

def place (j : Fin width) : SourceEquationLookup.Tape → Tape width Extra
  | .source => .source | .index => .index | .work => .work | .scratch => .scratch
  | .field s => .field j s

def fill (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) : Tape width Extra → List Bool
  | .source => localTapes .source | .index => localTapes .index
  | .work => localTapes .work | .scratch => localTapes .scratch
  | .field i s => if i = j then localTapes (.field s) else base (.field i s)
  | p => base p

@[simp] theorem fill_place (j : Fin width) (base : Tape width Extra → List Bool)
    (localTapes : SourceEquationLookup.Tape → List Bool) (p : SourceEquationLookup.Tape) :
    fill j base localTapes (place j p) = localTapes p := by
  cases p <;> simp [fill, place]

@[simp] theorem fill_self (j : Fin width) (base : Tape width Extra → List Bool) :
    fill j base (base ∘ place j) = base := by
  funext p
  cases p <;> simp [fill, place]
  intro h
  subst h
  rfl

variable [DecidableEq Extra]

def coordinateOutput {n : Nat} (j : Fin width) (equation : CloneGap.Equation (Fin n))
    (base : Tape width Extra → List Bool) : Tape width Extra → List Bool
  | .index | .work => []
  | .field k s => if k = j then
      encodeWord ((equationWords equation)[s.val]'(by simp)) ++ base (.field k s)
    else base (.field k s)
  | p => base p

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_savedIndex {n : Nat} (j k : Fin width) (equation : CloneGap.Equation (Fin n))
    (base : Tape width Extra → List Bool) :
    coordinateOutput j equation base (.savedIndex k) = base (.savedIndex k) := rfl

omit [DecidableEq Extra] in
@[simp] theorem coordinateOutput_field {n : Nat} (j : Fin width) (s : Fin 4)
    (equation : CloneGap.Equation (Fin n)) (base : Tape width Extra → List Bool) :
    coordinateOutput j equation base (.field j s) =
      encodeWord ((equationWords equation)[s.val]'(by simp)) ++ base (.field j s) := by
  simp [coordinateOutput]

def nameField (j : Fin width) (s : Fin 3) : Tape width Extra := .field j (nameSlot s)

end DFVSGames.Reduction.MachineSourceTuple
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineAddressHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineAddressHeaders

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineComposition

namespace Prefix

variable {K Λ σ : Type} [DecidableEq K]

def resultTapes (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base (slots 1) [])
    (slots 2) (encodeWord n ++ base (slots 2))) (slots 3) (encodeWord m ++ base (slots 3))

theorem resultTapes_other (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat)
    (tape : K) (hw : tape ≠ slots 1) (hn : tape ≠ slots 2) (hm : tape ≠ slots 3) :
    resultTapes slots base n m tape = base tape := by simp [resultTapes, hw, hn, hm]

@[simp] theorem resultTapes_source (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 0) = base (slots 0) := by
  simp [resultTapes, slots.injective.eq_iff]

@[simp] theorem resultTapes_work (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 1) = [] := by simp [resultTapes]

@[simp] theorem resultTapes_n (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 2) = encodeWord n ++ base (slots 2) := by
  simp [resultTapes, slots.injective.eq_iff]

@[simp] theorem resultTapes_m (slots : Fin 5 ↪ K) (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots 3) = encodeWord m ++ base (slots 3) := by
  simp [resultTapes]

end Prefix

noncomputable section

namespace Arithmetic

abbrev Coefficients (k s d noiseCount : Nat) :=
  Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount .capacity)) ⊕
    Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount .edges))

abbrev Layout (k s d noiseCount : Nat) := Control ⊕ Coefficients k s d noiseCount

def coefficientBlock (k s d noiseCount : Nat) (kind : Kind) :
    Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪
      Coefficients k s d noiseCount :=
  match kind with
  | .capacity => ⟨Sum.inl, Sum.inl_injective⟩
  | .edges => ⟨Sum.inr, Sum.inr_injective⟩

def localSlots (k s d noiseCount : Nat) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪
      Layout k s d noiseCount where
  toFun
    | .inl i => .inl (controlSlots kind i)
    | .inr i => .inr (coefficientBlock k s d noiseCount kind i)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl ((controlSlots kind).injective (Sum.inl.inj h))
      | inr b => cases h
    | inr a =>
      cases b with
      | inl b => cases h
      | inr b =>
        exact congrArg Sum.inr ((coefficientBlock k s d noiseCount kind).injective (Sum.inr.inj h))

variable {k s d noiseCount : Nat} {K Λ σ : Type}

def control (slots : Layout k s d noiseCount ↪ K) (c : Control) : K := slots (.inl c)

def evalSlots (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    MachineHorner.Layout (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind)) ↪ K :=
  (localSlots k s d noiseCount kind).trans slots

@[simp] theorem control_eq_iff (slots : Layout k s d noiseCount ↪ K) (a b : Control) :
    control slots a = control slots b ↔ a = b := by simp [control, slots.injective.eq_iff]

@[simp] theorem evalSlots_radix (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 0) = control slots (inputControl kind) := rfl
@[simp] theorem evalSlots_accA (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 1) = control slots .accA := rfl
@[simp] theorem evalSlots_accB (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 2) = control slots .accB := rfl
@[simp] theorem evalSlots_destination (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 3) = control slots (outputControl kind) := rfl
@[simp] theorem evalSlots_counter (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 4) = control slots .counter := rfl
@[simp] theorem evalSlots_scratch (slots : Layout k s d noiseCount ↪ K) (kind : Kind) :
    evalSlots slots kind (.inl 5) = control slots .scratch := rfl
@[simp] theorem evalSlots_digit (slots : Layout k s d noiseCount ↪ K) (kind : Kind)
    (i : Fin (CookLevin.PolynomialMachine.width (polynomial k s d noiseCount kind))) :
    evalSlots slots kind (.inr i) = slots (.inr (coefficientBlock k s d noiseCount kind i)) := rfl

variable [DecidableEq K]

def headerBits (k s d noiseCount n m : Nat) : List Bool :=
  encodeWords [2 * capacity k s d n m, 2 ^ s, edgeCount k s d noiseCount m]

def resultTapes (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Function.update (Function.update (Function.update base
    (control slots .baseValue) (encodeWord (radix s d n m)))
    (control slots .capacity) (encodeWord (capacity k s d n m)))
    (control slots .reversed) ((headerBits k s d noiseCount n m).reverse ++ base (control slots .reversed))

end Arithmetic

abbrev Layout (k s d noiseCount : Nat) := Fin 2 ⊕ Arithmetic.Layout k s d noiseCount

variable {k s d noiseCount : Nat} {K Λ σ : Type} [DecidableEq K]

def arithmeticSlots (slots : Layout k s d noiseCount ↪ K) :
    Arithmetic.Layout k s d noiseCount ↪ K :=
  (⟨Sum.inr, Sum.inr_injective⟩ : Arithmetic.Layout k s d noiseCount ↪
    Layout k s d noiseCount).trans slots

def prefixLocal (k s d noiseCount : Nat) : Fin 5 ↪ Layout k s d noiseCount where
  toFun i := match i.val with
    | 0 => .inl 0 | 1 => .inl 1
    | 2 => .inr (.inl .variableCount)
    | 3 => .inr (.inl .occurrenceCount)
    | _ => .inr (.inl .scratch)
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> cases h <;> rfl

def prefixSlots (slots : Layout k s d noiseCount ↪ K) : Fin 5 ↪ K :=
  (prefixLocal k s d noiseCount).trans slots

omit [DecidableEq K] in
theorem prefixSlots_apply (slots : Layout k s d noiseCount ↪ K) (index : Fin 5) :
    prefixSlots slots index = slots (match index.val with
      | 0 => .inl 0 | 1 => .inl 1
      | 2 => .inr (.inl .variableCount)
      | 3 => .inr (.inl .occurrenceCount)
      | _ => .inr (.inl .scratch)) := rfl

theorem prefixResult_control (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) (c : Arithmetic.Control)
    (hn : c ≠ .variableCount) (hm : c ≠ .occurrenceCount) :
    Prefix.resultTapes (prefixSlots slots) base n m
      (Arithmetic.control (arithmeticSlots slots) c) =
    base (Arithmetic.control (arithmeticSlots slots) c) := by
  apply Prefix.resultTapes_other <;>
    simp [prefixSlots_apply, Arithmetic.control, arithmeticSlots,
      slots.injective.eq_iff, hn, hm]

def resultTapes (slots : Layout k s d noiseCount ↪ K) (base : K → List Bool)
    (n m : Nat) : K → List Bool :=
  Arithmetic.resultTapes (arithmeticSlots slots)
    (Prefix.resultTapes (prefixSlots slots) base n m) n m

@[simp] theorem resultTapes_source (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (slots (.inl 0)) = base (slots (.inl 0)) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_n (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .variableCount) =
      encodeWord n ++ base (Arithmetic.control (arithmeticSlots slots) .variableCount) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_m (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) =
      encodeWord m ++ base (Arithmetic.control (arithmeticSlots slots) .occurrenceCount) := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

@[simp] theorem resultTapes_base (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .baseValue) =
      encodeWord (radix s d n m) := by simp [resultTapes, Arithmetic.resultTapes]

@[simp] theorem resultTapes_capacity (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .capacity) =
      encodeWord (capacity k s d n m) := by simp [resultTapes, Arithmetic.resultTapes]

@[simp] theorem resultTapes_reversed (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) :
    resultTapes slots base n m (Arithmetic.control (arithmeticSlots slots) .reversed) =
      (Arithmetic.headerBits k s d noiseCount n m).reverse ++
        base (Arithmetic.control (arithmeticSlots slots) .reversed) := by
  simp [resultTapes, Arithmetic.resultTapes,
    prefixResult_control slots base n m .reversed (by decide) (by decide)]

@[simp] theorem resultTapes_readCopy (slots : Layout k s d noiseCount ↪ K)
    (base : K → List Bool) (n m : Nat) : resultTapes slots base n m (slots (.inl 1)) = [] := by
  simp [resultTapes, Arithmetic.resultTapes, Prefix.resultTapes,
    prefixSlots_apply, arithmeticSlots, Arithmetic.control, slots.injective.eq_iff]

end

end DFVSGames.Reduction.MachineAddressHeaders
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_CanonicalWordTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.CanonicalBodyTemplate

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding
open scoped BigOperators

variable {k : Nat}

theorem flatMap_encodeWord (fields : Fin k → Fin 4 → Nat) (tokens : List (Token k)) :
    tokens.flatMap (fun token => encodeWord (evalToken fields token)) =
      encodeWords (evalTemplate fields tokens) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
    simp only [List.flatMap_cons, evalTemplate, List.map_cons, encodeWords]
    exact congrArg (List.append (encodeWord (evalToken fields token))) ih

end DFVSGames.Reduction.CanonicalBodyTemplate
end

section

namespace DFVSGames.Reduction.CanonicalBodyMachine

open Integration.BinaryLinear Foundations.Complexity CanonicalEncoding

variable {k : Nat}

def savedFields (fields : Fin k → Fin 4 → Nat) (index : Fin (4*k)) : List Bool :=
  encodeWord (fields ((fieldEquiv k).symm index).1 ((fieldEquiv k).symm index).2)

@[simp] theorem savedFields_fieldIndex (fields : Fin k → Fin 4 → Nat)
    (position : Fin k) (field : Fin 4) :
    savedFields fields (fieldIndex position field) = encodeWord (fields position field) := by
  simp [savedFields, fieldIndex]

def lowerToken : CanonicalBodyTemplate.Token k → MachineFieldTemplate.Token (4*k)
  | .literal value => .literal (encodeWord value)
  | .field position field => .copy (fieldIndex position field)

def lowerTemplate (tokens : List (CanonicalBodyTemplate.Token k)) :
    List (MachineFieldTemplate.Token (4*k)) := tokens.map lowerToken

@[simp] theorem lowerTemplate_length (tokens : List (CanonicalBodyTemplate.Token k)) :
    (lowerTemplate tokens).length = tokens.length := List.length_map _

theorem tokenOutput_lowerToken (fields : Fin k → Fin 4 → Nat)
    (token : CanonicalBodyTemplate.Token k) :
    MachineFieldTemplate.tokenOutput (savedFields fields) (lowerToken token) =
      encodeWord (CanonicalBodyTemplate.evalToken fields token) := by
  cases token <;>
    simp [lowerToken, MachineFieldTemplate.tokenOutput, CanonicalBodyTemplate.evalToken]

theorem templateOutput_lowerTemplate (fields : Fin k → Fin 4 → Nat)
    (tokens : List (CanonicalBodyTemplate.Token k)) :
    MachineFieldTemplate.templateOutput (lowerTemplate tokens) (savedFields fields) =
      encodeWords (CanonicalBodyTemplate.evalTemplate fields tokens) := by
  simp only [MachineFieldTemplate.templateOutput, lowerTemplate, List.flatMap_map,
    tokenOutput_lowerToken]
  exact CanonicalBodyTemplate.flatMap_encodeWord fields tokens

def template {k s d : Nat} (z : Ambient s d) (a : Fin k → Fin 3 → Ambient s d)
    (b : Fin k → F2) : List (MachineFieldTemplate.Token (4*k)) :=
  lowerTemplate (CanonicalBodyTemplate.template z a b)

@[simp] theorem template_length {k s d : Nat} (z : Ambient s d)
    (a : Fin k → Fin 3 → Ambient s d) (b : Fin k → F2) :
    (template z a b).length = 1 + 9*k := by
  simp [template]

end DFVSGames.Reduction.CanonicalBodyMachine
end

section

namespace DFVSGames.Reduction.AddressMachineSpace

open DFVSGames.Foundations.Complexity

abbrev Extra (k s d noiseCount : Nat) :=
  MachineAddressHeaders.Arithmetic.Layout k s d noiseCount ⊕
    (MachineTemplateAddress.Tape (4 * k) (1 + 9 * k) ⊕ (Fin k ⊕ Unit))

abbrev Tape (k s d noiseCount : Nat) :=
  MachineSourceTuple.Tape k (Extra k s d noiseCount)

variable (k s d noiseCount : Nat)

def headerArithmeticSlots : MachineAddressHeaders.Arithmetic.Layout k s d noiseCount ↪
    Tape k s d noiseCount where
  toFun a := .extra (.inl a)
  inj' := by intro a b h; exact Sum.inl.inj (MachineSourceTuple.Tape.extra.inj h)

def headerTape (c : MachineAddressHeaders.Arithmetic.Control) : Tape k s d noiseCount :=
  .extra (.inl (.inl c))

@[simp] theorem headerTape_eq_iff (a b : MachineAddressHeaders.Arithmetic.Control) :
    headerTape k s d noiseCount a = headerTape k s d noiseCount b ↔ a = b := by
  simp [headerTape]

def fullHeaderSlots : MachineAddressHeaders.Layout k s d noiseCount ↪ Tape k s d noiseCount where
  toFun
    | .inl 0 => .source
    | .inl 1 => .work
    | .inr a => headerArithmeticSlots k s d noiseCount a
  inj' := by
    rintro (a | a) (b | b) h
    · fin_cases a <;> fin_cases b <;> cases h <;> rfl
    · fin_cases a <;> cases h
    · fin_cases b <;> cases h
    · exact congrArg Sum.inr ((headerArithmeticSlots k s d noiseCount).injective h)

@[simp] theorem fullHeaderSlots_source : fullHeaderSlots k s d noiseCount (.inl 0) = .source := rfl
@[simp] theorem fullHeaderSlots_work : fullHeaderSlots k s d noiseCount (.inl 1) = .work := rfl
@[simp] theorem fullHeaderSlots_arithmetic (a : MachineAddressHeaders.Arithmetic.Layout k s d noiseCount) :
    fullHeaderSlots k s d noiseCount (.inr a) = headerArithmeticSlots k s d noiseCount a := rfl

@[simp] theorem arithmeticSlots_fullHeaderSlots :
    MachineAddressHeaders.arithmeticSlots (fullHeaderSlots k s d noiseCount) =
      headerArithmeticSlots k s d noiseCount := by ext a; rfl

def prefixSlots : Fin 5 ↪ Tape k s d noiseCount :=
  MachineAddressHeaders.prefixSlots (fullHeaderSlots k s d noiseCount)

@[simp] theorem prefixSlots_source : prefixSlots k s d noiseCount 0 = .source := rfl
@[simp] theorem prefixSlots_work : prefixSlots k s d noiseCount 1 = .work := rfl
@[simp] theorem prefixSlots_variables :
    prefixSlots k s d noiseCount 2 = headerTape k s d noiseCount .variableCount := rfl
@[simp] theorem prefixSlots_occurrences :
    prefixSlots k s d noiseCount 3 = headerTape k s d noiseCount .occurrenceCount := rfl
@[simp] theorem prefixSlots_scratch :
    prefixSlots k s d noiseCount 4 = headerTape k s d noiseCount .scratch := rfl

def canonicalField (position : Fin k) (slot : Fin 4) : Tape k s d noiseCount :=
  if slot = 3 then .savedIndex position else .field position slot

@[simp] theorem canonicalField_occurrence (position : Fin k) :
    canonicalField k s d noiseCount position 3 = .savedIndex position := by simp [canonicalField]

@[simp] theorem canonicalField_name (position : Fin k) (slot : Fin 3) :
    canonicalField k s d noiseCount position (MachineSourceTuple.nameSlot slot) =
      MachineSourceTuple.nameField position slot := by
  have hs : MachineSourceTuple.nameSlot slot ≠ (3 : Fin 4) := by
    intro h
    have hv := congrArg Fin.val h
    have bound := slot.isLt
    simp only [MachineSourceTuple.nameSlot] at hv
    omega
  simp [canonicalField, hs, MachineSourceTuple.nameField]

def privateAddress (tape : MachineTemplateAddress.Tape (4 * k) (1 + 9 * k)) :
    Tape k s d noiseCount := .extra (.inr (.inl tape))

def edgeSlot : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) → Tape k s d noiseCount
  | .inl (.field i) => canonicalField k s d noiseCount
      ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2
  | .inl .radix => headerTape k s d noiseCount .baseValue
  | .inl tape => privateAddress k s d noiseCount tape
  | .inr i => if i = 0 then headerTape k s d noiseCount .capacity
      else headerTape k s d noiseCount .reversed

def edgeDecode_inline_AddressMachineSpace : Tape k s d noiseCount →
    Option (MachineAddressEdge.Tape (4 * k) (1 + 9 * k))
  | .savedIndex j => some (.inl (.field (CanonicalBodyMachine.fieldIndex j 3)))
  | .field j slot => if slot = 3 then none
      else some (.inl (.field (CanonicalBodyMachine.fieldIndex j slot)))
  | .extra (.inl (.inl .baseValue)) => some (.inl .radix)
  | .extra (.inl (.inl .capacity)) => some (.inr 0)
  | .extra (.inl (.inl .reversed)) => some (.inr 1)
  | .extra (.inr (.inl tape)) => some (.inl tape)
  | _ => none

theorem edgeDecode_canonicalField_inline_AddressMachineSpace (position : Fin k) (slot : Fin 4) :
    edgeDecode_inline_AddressMachineSpace k s d noiseCount (canonicalField k s d noiseCount position slot) =
      some (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) := by
  by_cases h : slot = 3 <;> simp [canonicalField, edgeDecode_inline_AddressMachineSpace, h]

theorem edgeDecode_edgeSlot_inline_AddressMachineSpace (tape : MachineAddressEdge.Tape (4 * k) (1 + 9 * k)) :
    edgeDecode_inline_AddressMachineSpace k s d noiseCount (edgeSlot k s d noiseCount tape) = some tape := by
  rcases tape with tape | i
  · cases tape <;> try rfl
    rename_i index
    rw [edgeSlot, edgeDecode_canonicalField_inline_AddressMachineSpace]
    exact congrArg (fun i => some (Sum.inl (MachineTemplateAddress.Tape.field i)))
      ((CanonicalBodyMachine.fieldEquiv k).apply_symm_apply index)
  · fin_cases i <;> rfl

def addressEdgeSlots : MachineAddressEdge.Tape (4 * k) (1 + 9 * k) ↪ Tape k s d noiseCount where
  toFun := edgeSlot k s d noiseCount
  inj' := by
    intro a b h
    have decoded := congrArg (edgeDecode_inline_AddressMachineSpace k s d noiseCount) h
    apply Option.some.inj
    simpa only [edgeDecode_edgeSlot_inline_AddressMachineSpace] using decoded

@[simp] theorem addressEdgeSlots_fieldIndex (position : Fin k) (slot : Fin 4) :
    addressEdgeSlots k s d noiseCount
      (.inl (.field (CanonicalBodyMachine.fieldIndex position slot))) =
        canonicalField k s d noiseCount position slot := by
  change canonicalField k s d noiseCount
    ((CanonicalBodyMachine.fieldEquiv k).symm
      (CanonicalBodyMachine.fieldEquiv k (position, slot))).1
    ((CanonicalBodyMachine.fieldEquiv k).symm
      (CanonicalBodyMachine.fieldEquiv k (position, slot))).2 = _
  simp only [Equiv.symm_apply_apply]

@[simp] theorem addressSlots_name (position : Fin k) (slot : Fin 3) :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
      (.field (CanonicalBodyMachine.fieldIndex position (MachineSourceTuple.nameSlot slot))) =
        MachineSourceTuple.nameField position slot := by
  exact (addressEdgeSlots_fieldIndex k s d noiseCount position _).trans
    (canonicalField_name k s d noiseCount position slot)

@[simp] theorem addressSlots_occurrence (position : Fin k) :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount)
      (.field (CanonicalBodyMachine.fieldIndex position 3)) = .savedIndex position := by
  exact (addressEdgeSlots_fieldIndex k s d noiseCount position 3).trans
    (canonicalField_occurrence k s d noiseCount position)

@[simp] theorem addressSlots_radix :
    MachineAddressEdge.addressSlots (addressEdgeSlots k s d noiseCount) .radix =
      headerTape k s d noiseCount .baseValue := rfl
@[simp] theorem addressSlots_capacity :
    MachineAddressEdge.capacityTape (addressEdgeSlots k s d noiseCount) =
      headerTape k s d noiseCount .capacity := rfl
@[simp] theorem addressSlots_output :
    MachineAddressEdge.outputTape (addressEdgeSlots k s d noiseCount) =
      headerTape k s d noiseCount .reversed := rfl

def current (j : Fin k) : Tape k s d noiseCount := .savedIndex j.rev
def remaining (j : Fin k) : Tape k s d noiseCount := .extra (.inr (.inr (.inl j)))
def finalOutput : Tape k s d noiseCount := .extra (.inr (.inr (.inr ())))

@[simp] theorem current_rev (j : Fin k) : current k s d noiseCount j.rev = .savedIndex j := by
  simp [current]

def odometerSlots : MachineOdometerInit.Tape k ↪ Tape k s d noiseCount where
  toFun
    | .radix => headerTape k s d noiseCount .occurrenceCount
    | .scratch => .copyScratch
    | .current j => current k s d noiseCount j
    | .remaining j => remaining k s d noiseCount j
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp_all [headerTape, current, remaining]

@[simp] theorem odometerSlots_radix : odometerSlots k s d noiseCount .radix =
    headerTape k s d noiseCount .occurrenceCount := rfl
@[simp] theorem odometerSlots_scratch : odometerSlots k s d noiseCount .scratch = .copyScratch := rfl
@[simp] theorem odometerSlots_current (j : Fin k) :
    odometerSlots k s d noiseCount (.current j) = .savedIndex j.rev := rfl
@[simp] theorem odometerSlots_remaining (j : Fin k) :
    odometerSlots k s d noiseCount (.remaining j) = remaining k s d noiseCount j := rfl

end DFVSGames.Reduction.AddressMachineSpace
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleLoaded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Integration.AddressTupleCleanup

open Turing DFVSGames.Reduction DFVSGames.Foundations.Complexity

variable (k s d noiseCount : Nat)

def loadedFields : List (AddressMachineSpace.Tape k s d noiseCount) :=
  List.ofFn (fun i : Fin (4 * k) =>
    MachineSourceTuple.Tape.field ((CanonicalBodyMachine.fieldEquiv k).symm i).1
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2)

@[simp] theorem loadedFields_length : (loadedFields k s d noiseCount).length = 4 * k := by
  simp only [loadedFields, List.length_ofFn]

theorem mem_loadedFields (tape : AddressMachineSpace.Tape k s d noiseCount) :
    tape ∈ loadedFields k s d noiseCount ↔
      ∃ position : Fin k, ∃ slot : Fin 4, tape = .field position slot := by
  unfold loadedFields
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact ⟨((CanonicalBodyMachine.fieldEquiv k).symm i).1,
      ((CanonicalBodyMachine.fieldEquiv k).symm i).2, hi.symm⟩
  · rintro ⟨position, slot, rfl⟩
    apply List.mem_ofFn.mpr
    refine ⟨CanonicalBodyMachine.fieldEquiv k (position, slot), ?_⟩
    simp only [Equiv.symm_apply_apply]

abbrev Label := MachineDrainMany.Label (loadedFields k s d noiseCount)

noncomputable abbrev cleared (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :=
  MachineDrainMany.finalTapes (loadedFields k s d noiseCount) base

@[simp] theorem cleared_field (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) (slot : Fin 4) :
    cleared k s d noiseCount base (.field position slot) = [] :=
  MachineDrainMany.finalTapes_mem (loadedFields k s d noiseCount) base (.field position slot)
    ((mem_loadedFields k s d noiseCount _).2 ⟨position, slot, rfl⟩)

theorem cleared_outside (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (tape : AddressMachineSpace.Tape k s d noiseCount)
    (outside : ∀ position : Fin k, ∀ slot : Fin 4, tape ≠ .field position slot) :
    cleared k s d noiseCount base tape = base tape := by
  apply MachineDrainMany.finalTapes_not_mem
  intro h
  obtain ⟨position, slot, same⟩ := (mem_loadedFields k s d noiseCount tape).1 h
  exact outside position slot same

@[simp] theorem cleared_source (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .source = base .source := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_savedIndex
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) (position : Fin k) :
    cleared k s d noiseCount base (.savedIndex position) = base (.savedIndex position) := by
  apply cleared_outside
  intro other slot h
  cases h

@[simp] theorem cleared_extra (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (extra : AddressMachineSpace.Extra k s d noiseCount) :
    cleared k s d noiseCount base (.extra extra) = base (.extra extra) := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_index (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .index = base .index := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_work (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .work = base .work := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_scratch (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .scratch = base .scratch := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_copyScratch (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base .copyScratch = base .copyScratch := by
  apply cleared_outside
  intro position slot h
  cases h

@[simp] theorem cleared_headerTape
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (header : MachineAddressHeaders.Arithmetic.Control) :
    cleared k s d noiseCount base (AddressMachineSpace.headerTape k s d noiseCount header) =
      base (AddressMachineSpace.headerTape k s d noiseCount header) := by
  simpa only [AddressMachineSpace.headerTape, AddressMachineSpace.headerArithmeticSlots] using
    cleared_extra k s d noiseCount base (.inl (.inl header))

@[simp] theorem cleared_current (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) :
    cleared k s d noiseCount base (AddressMachineSpace.current k s d noiseCount position) =
      base (AddressMachineSpace.current k s d noiseCount position) := by
  simpa only [AddressMachineSpace.current] using
    cleared_savedIndex k s d noiseCount base position.rev

@[simp] theorem cleared_remaining (base : AddressMachineSpace.Tape k s d noiseCount → List Bool)
    (position : Fin k) :
    cleared k s d noiseCount base (AddressMachineSpace.remaining k s d noiseCount position) =
      base (AddressMachineSpace.remaining k s d noiseCount position) := by
  simpa only [AddressMachineSpace.remaining] using
    cleared_extra k s d noiseCount base (.inr (.inr (.inl position)))

@[simp] theorem cleared_finalOutput
    (base : AddressMachineSpace.Tape k s d noiseCount → List Bool) :
    cleared k s d noiseCount base (AddressMachineSpace.finalOutput k s d noiseCount) =
      base (AddressMachineSpace.finalOutput k s d noiseCount) := by
  simpa only [AddressMachineSpace.finalOutput] using
    cleared_extra k s d noiseCount base (.inr (.inr (.inr ())))

end DFVSGames.Integration.AddressTupleCleanup
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineOutcomeRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.MachineOutcomeRows

open Turing
open DFVSGames.Foundations.Complexity

structure Spec (q width : Nat) where
  left : List (MachineFieldTemplate.Token q)
  right : List (MachineFieldTemplate.Token q)
  permutation : List Bool

abbrev Row (k q width : Nat) := Rhs k → Spec q width

variable {k q width : Nat} {K Λ σ : Type} [DecidableEq K]

abbrev LocalLabel (slots : MachineAddressEdge.Tape q width ↪ K) (row : Spec q width) :=
  MachineAddressEdge.Label row.left.length row.right.length width
    (MachineTemplateAddress.chosen (MachineAddressEdge.addressSlots slots))

def selected (rows : List (Row k q width)) (rhs : Rhs k) : List (Spec q width) :=
  rows.map (fun row => row rhs)

@[simp] theorem selected_length (rows : List (Row k q width)) (rhs : Rhs k) :
    (selected rows rhs).length = rows.length := by simp [selected]

abbrev Label (slots : MachineAddressEdge.Tape q width ↪ K) (rows : List (Row k q width)) :=
  Unit ⊕ (Σ rhs : Rhs k, MachineFiniteSequence.Label (LocalLabel slots) (selected rows rhs))

end DFVSGames.Reduction.MachineOutcomeRows
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_UniformReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.AddressGame

open ActualSource
open Foundations.Target
open Integration.VertexEmbedding

def addressEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : ActualGame.Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := queryAddress S k s d false (ActualGame.leftQuery S k g ω)
  target := queryAddress S k s d true (ActualGame.rightQuery S k g ω)
  permutation := Encoding.translationTable
    (ActualGame.offset S k s d (ActualGame.leftQuery S k g ω))
    (ActualGame.offset S k s d (ActualGame.rightQuery S k g ω))

@[simp] theorem addressEdge_permutation (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    (addressEdge S k g ω).permutation = (ActualGame.explicitEdge S k g ω).permutation := rfl

def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (addressEdge S k g)
  nonempty h := by
    have hempty := List.map_eq_nil_iff.mp h
    apply (ActualGame.outputInstanceWithEnumeration S k g en).nonempty
    change (ActualGame.explicitOutcomes S k g en).map (ActualGame.explicitEdge S k g) = []
    rw [hempty]
    rfl

@[simp] theorem outputInstance_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstance S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstance, List.length_map, ActualGame.explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

end DFVSGames.Reduction.AddressGame
end

section

namespace DFVSGames.Reduction.FixedOutcomes

open Integration.BinaryLinear ActualHomogeneous ActualSource
open ActualEnumeration _root_.OAI.DFVSGames.Reduction.Explicit

variable {N : Type*}

abbrev Parameter (k s d : Nat) (N : Type*) :=
  (E k →ₗ[F2] ActualEnumeration.Ambient s d) × (N × (E k →ₗ[F2] F2))

def fixedParams (k s d : Nat) (indices : List N) : List (Parameter k s d N) :=
  pairs (allLinearMaps k _ (ambientVectors s d))
    (pairs indices (allLinearMaps k F2 [0, 1]))

theorem fixedParams_length (k s d : Nat) (indices : List N) :
    (fixedParams k s d indices).length = 2^((2*k+1)*(s+d+1)) * indices.length := by
  simp only [fixedParams, length_pairs, length_allLinearMaps, length_ambientVectors,
    List.length_cons, List.length_nil, ← pow_mul]
  change 2^((s+d)*(2*k+1)) * (indices.length * 2^(2*k+1)) =
    2^((2*k+1)*(s+d+1)) * indices.length
  rw [show (2*k+1)*(s+d+1) = (s+d)*(2*k+1)+(2*k+1) by ring, pow_add]
  ring

def tableParams (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    List (Parameter k s d (Fin T.vectors.length)) :=
  fixedParams k s d (List.finRange T.vectors.length)

theorem tableParams_length (k : Nat) {s d : Nat} (T : Integration.NoiseTables.Table s d) :
    (tableParams k T).length = 2^((2*k+1)*(s+d+1)) * T.vectors.length := by
  simp only [tableParams, fixedParams_length, List.length_finRange]

end DFVSGames.Reduction.FixedOutcomes
end

section

namespace DFVSGames.Reduction.AddressByteSemantics

open Integration.BinaryLinear Foundations.Complexity ActualSource

def queryWords {k s d : Nat} (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) : List Nat :=
  CanonicalBodyTemplate.evalTemplate fields
    (CanonicalBodyTemplate.template (X (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple X) b)

def permutationWords {k s d : Nat} (X Y : ActualGame.Map k s d)
    (b : Fin k → F2) : List Nat :=
  tableWords (Encoding.translationTable
    (CanonicalBodyTemplate.alphabetOffset (X (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple X) b)
    (CanonicalBodyTemplate.alphabetOffset (Y (ActualHomogeneous.hBasis k))
      (ActualCanonical.standardTriple Y) b))

@[simp] theorem queryWords_length {k s d : Nat} (fields : Fin k → Fin 4 → Nat)
    (X : ActualGame.Map k s d) (b : Fin k → F2) :
    (queryWords fields X b).length = 1 + 9*k := by
  simp only [queryWords, CanonicalBodyTemplate.evalTemplate, List.length_map,
    CanonicalBodyTemplate.template_length]

@[simp] theorem permutationWords_length {k s d : Nat} (X Y : ActualGame.Map k s d)
    (b : Fin k → F2) : (permutationWords X Y b).length = 2^s :=
  tableWords_length _

end DFVSGames.Reduction.AddressByteSemantics
end

section

namespace DFVSGames.Reduction.AddressOutcomeSpecs

open Integration.BinaryLinear Foundations.Complexity ActualSource
open Integration

abbrev Spec (k : Nat) := MachineOutcomeRows.Spec (4*k) (1+9*k)
abbrev Parameter (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :=
  FixedOutcomes.Parameter k s d (Fin T.vectors.length)

def bitVector {k : Nat} (b : Fin k → Bool) : Fin k → F2 := fun j => ofBit (b j)

def rightMap {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T) :
    ActualGame.Map k s d := p.1 + p.2.2.smulRight (T.vectors.get p.2.1)

def row {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) : Spec k where
  left := CanonicalBodyMachine.template (p.1 (ActualHomogeneous.hBasis k))
    (ActualCanonical.standardTriple p.1) (bitVector b)
  right := CanonicalBodyMachine.template (rightMap T p (ActualHomogeneous.hBasis k))
    (ActualCanonical.standardTriple (rightMap T p)) (bitVector b)
  permutation := encodeWords (AddressByteSemantics.permutationWords p.1 (rightMap T p) (bitVector b))

def rows (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    List (MachineOutcomeRows.Row k (4*k) (1+9*k)) :=
  (FixedOutcomes.tableParams k T).map (row T)

@[simp] theorem row_left_length {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) : (row T p b).left.length = 1+9*k :=
  CanonicalBodyMachine.template_length _ _ _

@[simp] theorem row_right_length {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) : (row T p b).right.length = 1+9*k :=
  CanonicalBodyMachine.template_length _ _ _

@[simp] theorem rows_length (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    (rows k T).length = 2^((2*k+1)*(s+d+1)) * T.vectors.length := by
  simp only [rows, List.length_map, FixedOutcomes.tableParams_length]

@[simp] theorem selected_rows (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (b : Fin k → Bool) :
    MachineOutcomeRows.selected (rows k T) b =
      (FixedOutcomes.tableParams k T).map (fun p => row T p b) := by
  simp only [MachineOutcomeRows.selected, rows, List.map_map, Function.comp_def]

def interpreted (width : Nat) (bits : List Bool) : {words : List Nat // words.length = width} :=
  let words := (decodeWords bits).getD []
  if h : words.length = width then ⟨words, h⟩
  else ⟨List.replicate width 0, List.length_replicate⟩

theorem interpreted_encoded (width : Nat) (words : List Nat) (hlen : words.length = width) :
    (interpreted width (encodeWords words)).val = words := by
  simp [interpreted, hlen]

def values {k : Nat} (fields : Fin k → Fin 4 → Nat) (spec : Spec k) : Values k where
  left := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields))).val
  right := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields))).val
  left_length := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.left (CanonicalBodyMachine.savedFields fields))).property
  right_length := (interpreted (1+9*k)
    (MachineFieldTemplate.templateOutput spec.right (CanonicalBodyMachine.savedFields fields))).property

theorem row_left_output {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    MachineFieldTemplate.templateOutput (row T p b).left (CanonicalBodyMachine.savedFields fields) =
      encodeWords (AddressByteSemantics.queryWords fields p.1 (bitVector b)) :=
  CanonicalBodyMachine.templateOutput_lowerTemplate fields _

theorem row_right_output {k s d : Nat} (T : NoiseTables.Table s d) (p : Parameter k T)
    (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    MachineFieldTemplate.templateOutput (row T p b).right (CanonicalBodyMachine.savedFields fields) =
      encodeWords (AddressByteSemantics.queryWords fields (rightMap T p) (bitVector b)) :=
  CanonicalBodyMachine.templateOutput_lowerTemplate fields _

@[simp] theorem values_row_left {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    (values fields (row T p b)).left =
      AddressByteSemantics.queryWords fields p.1 (bitVector b) := by
  change (interpreted (1+9*k) _).val = _
  rw [row_left_output]
  exact interpreted_encoded _ _ (AddressByteSemantics.queryWords_length _ _ _)

@[simp] theorem values_row_right {k s d : Nat} (T : NoiseTables.Table s d)
    (p : Parameter k T) (b : Fin k → Bool) (fields : Fin k → Fin 4 → Nat) :
    (values fields (row T p b)).right =
      AddressByteSemantics.queryWords fields (rightMap T p) (bitVector b) := by
  change (interpreted (1+9*k) _).val = _
  rw [row_right_output]
  exact interpreted_encoded _ _ (AddressByteSemantics.queryWords_length _ _ _)

def rhsBits (S : Source) {k : Nat} (U : ActualGame.Question S k) : Fin k → Bool :=
  fun j => (S.equation (U j)).rhs

@[simp] theorem bitVector_rhsBits (S : Source) {k : Nat} (U : ActualGame.Question S k) :
    bitVector (rhsBits S U) = fun j => ActualGame.rhs S (U j) := rfl

end DFVSGames.Reduction.AddressOutcomeSpecs
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AddressTupleBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Integration.AddressTupleBody

open Turing Reduction Foundations.Complexity
open AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

abbrev Arena (k s d noiseCount : Nat) := AddressMachineSpace.Tape k s d noiseCount
abbrev Rows (k : Nat) := List (MachineOutcomeRows.Row k (4*k) (1+9*k))
abbrev Slots (k s d noiseCount : Nat) := AddressMachineSpace.addressEdgeSlots k s d noiseCount
abbrev CleanupLabel (k s d noiseCount : Nat) :=
  AddressTupleCleanup.Label k s d noiseCount
abbrev RowLabel (k s d noiseCount : Nat) (rows : Rows k) :=
  MachineOutcomeRows.Label (Slots k s d noiseCount) rows
abbrev Label (k s d noiseCount : Nat) (rows : Rows k) :=
  MachineSourceTuple.Label k ⊕ (Unit ⊕
    (RowLabel k s d noiseCount rows ⊕ (CleanupLabel k s d noiseCount ⊕ Unit)))

variable {rows : Rows k}

def rhsLabel (labels : Label k s d noiseCount rows → Λ) : Λ := labels (.inr (.inl ()))
def cleanupLabels (labels : Label k s d noiseCount rows → Λ) : CleanupLabel k s d noiseCount → Λ :=
  fun l => labels (.inr (.inr (.inr (.inl l))))
def resetLabel (labels : Label k s d noiseCount rows → Λ) : Λ :=
  labels (.inr (.inr (.inr (.inr ()))))

def reset (exit : Option Λ) : TM2.Stmt (fun _ : Arena k s d noiseCount => Bool) Λ (BodyState k) :=
  .load (fun _ => initialState k) (MachineFieldTemplate.jump exit)

def source (F : SourceEncoding.Input) : ActualSource.Source :=
  ActualSource.Source.ofList F.equations F.nonempty

end DFVSGames.Integration.AddressTupleBody
end

section

namespace DFVSGames.Reduction.AddressMachineProgram

open Turing Foundations.Complexity Foundations.Hastad Integration
open MachineComposition

noncomputable section

abbrev Tape (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :=
  AddressMachineSpace.Tape k s d T.vectors.length

variable (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)

def accumulator : Tape k T := AddressMachineSpace.headerTape k s d T.vectors.length .reversed
def output : Tape k T := AddressMachineSpace.finalOutput k s d T.vectors.length

def clearKeys : List (Tape k T) := by
  classical
  exact ((Finset.univ : Finset (Tape k T)).filter
    (fun tape : Tape k T => tape ≠ accumulator k T ∧ tape ≠ output k T)).toList

@[simp] theorem mem_clearKeys (tape : Tape k T) :
    tape ∈ clearKeys k T ↔ tape ≠ accumulator k T ∧ tape ≠ output k T := by
  classical
  simp [clearKeys]

@[simp] theorem accumulator_not_mem_clearKeys : accumulator k T ∉ clearKeys k T := by simp

end
end DFVSGames.Reduction.AddressMachineProgram
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Machines_MachineSingleOrbitBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Appendix.CompressionCount

open Module
open DFVSGames.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

def base : (U × K) →ₗ[F2] (U × C) :=
  (LinearMap.inl F2 U C).comp (LinearMap.fst F2 U K)

@[simp] theorem base_apply (p : U × K) : base U K C p = (p.1, 0) := rfl

variable {U K C}

def compress (Y : (U × K) →ₗ[F2] (U × C)) : K →ₗ[F2] C :=
  (LinearMap.snd F2 U C).comp (Y.comp (LinearMap.inr F2 U K))

@[simp] theorem compress_apply (Y : (U × K) →ₗ[F2] (U × C)) (k : K) :
    compress Y k = (Y (0, k)).2 := rfl

abbrev Parameters (Z : K →ₗ[F2] C) :=
  (Z.range →ₗ[F2] U) × (U →ₗ[F2] Z.range)

def graph (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Z.range →ₗ[F2] (U × C) := F.prod Z.range.subtype

def lower (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    (U × K) →ₗ[F2] Z.range := H.coprod Z.rangeRestrict

def lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (U × K) →ₗ[F2] (U × C) :=
  base U K C + (graph Z P.1).comp (lower Z P.2)

@[simp] theorem lift_apply (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z)
    (p : U × K) :
    lift Z P p = (p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      ((P.2 p.1 : Z.range) : C) + Z p.2) := by
  simp [lift, graph, lower]

@[simp] theorem compress_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    compress (lift Z P) = Z := by
  ext k
  simp

end DFVSGames.Appendix.CompressionCount

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Games_AffineWitnessNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.MatrixCoordinates

open Integration.BinaryLinear Reduction
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable

local instance homFintype_rfda2c4_1 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
def domainCoordinates (k : ℕ) :
    ActualHomogeneous.E k ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  LinearEquiv.ofFinrankEq _ _ (by
    rw [ActualHomogeneous.finrank_E, Module.finrank_fin_fun])

def changeDomain {D E K : Type*} [AddCommGroup D] [Module F2 D]
    [AddCommGroup E] [Module F2 E] [AddCommGroup K] [Module F2 K]
    (e : D ≃ₗ[F2] E) : (D →ₗ[F2] K) ≃ₗ[F2] (E →ₗ[F2] K) where
  toFun M := M.comp e.symm.toLinearMap
  invFun M := M.comp e.toLinearMap
  left_inv M := by ext x; simp
  right_inv M := by ext x; simp
  map_add' M N := by ext x; rfl
  map_smul' c M := by ext x; rfl

def mapEquiv (k ell : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) ≃ₗ[F2]
      Inverse.Shortcode.Mat ell (1 + 2 * k) :=
  (changeDomain (domainCoordinates k)).trans LinearMap.toMatrix'

@[simp] theorem mapEquiv_apply (k ell : ℕ)
    (M : ActualHomogeneous.E k →ₗ[F2] (Fin ell → F2)) :
    mapEquiv k ell M = LinearMap.toMatrix' (M.comp (domainCoordinates k).symm.toLinearMap) :=
  rfl

@[simp] theorem mapEquiv_symm_apply (k ell : ℕ)
    (M : Inverse.Shortcode.Mat ell (1 + 2 * k)) :
    (mapEquiv k ell).symm M = (Matrix.toLin' M).comp (domainCoordinates k).toLinearMap :=
  rfl

def functionalEquiv (k : ℕ) :
    (ActualHomogeneous.E k →ₗ[F2] F2) ≃ₗ[F2] (Fin (1 + 2 * k) → F2) :=
  (changeDomain (domainCoordinates k)).trans ((Pi.basisFun F2 (Fin (1 + 2 * k))).constr F2).symm

@[simp] theorem functionalEquiv_apply (k : ℕ)
    (l : ActualHomogeneous.E k →ₗ[F2] F2) (j : Fin (1 + 2 * k)) :
    functionalEquiv k l j = l ((domainCoordinates k).symm (Pi.single j 1)) := by
  simp [functionalEquiv, changeDomain, Module.Basis.constr_symm_apply, Pi.basisFun_apply]

end
end DFVSGames.Decoder.MatrixCoordinates

end OAI
end

section
-- module Solutions.OAIQ085_DF.DirectedFeedback_Encoding_SelectedPolicies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DFVSGames.Decoder.ActualSeedEvents

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Fintype.ofFinite

local instance homFintype_rfda2c4_2 {D F : Type*}
    [AddCommGroup D] [Module F2 D] [AddCommGroup F] [Module F2 F]
    [Fintype D] [Fintype F] : Fintype (D →ₗ[F2] F) :=
  Fintype.ofInjective (fun M : D →ₗ[F2] F => (M : D → F)) DFunLike.coe_injective
abbrev Datum (S : Source) (k s d r : ℕ) :=
  AdviceLaw.CompleteData k (Fin S.occurrences) (Alphabet s) (Vector d) (Vector r)

end
end DFVSGames.Decoder.ActualSeedEvents

end OAI
end


