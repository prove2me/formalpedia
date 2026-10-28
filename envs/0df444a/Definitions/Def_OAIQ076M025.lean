-- Prove2me | Definitions.Def_OAIQ076M025
-- name    : OAIQ076M025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:19:55.049825+00:00
-- url     : https://prove2.me/theorems/224c09c3-a9fb-471f-8867-c68babb6b10b
-- title:
--   Definitions bundle OAIQ076M025 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 542 declarations of OpenAI's Lean: 182 definitions, 6 inductive types or structures, 1 instance and 353 theorems. The definitions and types are `OAI.MinUncutGames.Foundations.Complexity.MachineAffineLookup.finalTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineCloudPrefix.inputLength`, `OAI.MinUncutGames.Foundations.Complexity.MachineCloudSelect.remainder`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderRow.RowData.tableLength`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderRow.cleanupSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderRow.lookupPhaseLabel`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderRow.reversePhaseLabel`, `OAI.MinUncutGames.Foundations.Complexity.MachineExpanderRow.scanPhaseLabel`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.State`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.inputRowBits`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.recordsInput`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.recordsOutput`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.reindexInstruction`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.reindexMappedTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.reindexResultTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.reindexRowBits`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.reindexSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.rowBits`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.streamFrame`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.streamResultTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.streamRowSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyRows.vertexSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.inputBlocks`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.loopTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineLazyTable.prefixSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.State`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.instruction`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.resultTapes`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.rowBits`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.rowCostBound`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.rowSizeBound`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.rowSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.streamFrame`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.streamOutput`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.trueBits`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.vertexInstruction`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayRows.vertexSteps`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayTable.blockSize`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayTable.expanderBlock`, `OAI.MinUncutGames.Foundations.Complexity.MachineOverlayTable.expanderOutput` and 148 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Games_PoweringInitializeFrame`, `MinUncut_Games_PoweringPlanBudget`, `MinUncut_Games_PoweringPolynomialBudget`, `MinUncut_Machines_Alphabet`, `MinUncut_Machines_Driver`, `MinUncut_Machines_Input`, `MinUncut_Machines_MachineCloudPrefix`, `MinUncut_Machines_MachineCloudSelect`, `MinUncut_Machines_MachineDummyRows`, `MinUncut_Machines_MachineExpanderFamilyAffine`, `MinUncut_Machines_MachineExpanderFamilyCycle`, `MinUncut_Machines_MachineExpanderRowFrames`, `MinUncut_Machines_MachineExpanderTableProgram`, `MinUncut_Machines_MachineExpanderTableRows`, `MinUncut_Machines_MachineFiniteAlphabet`, `MinUncut_Machines_MachineFixedDivMod`, `MinUncut_Machines_MachineLazyRows`, `MinUncut_Machines_MachineLazyTable`, `MinUncut_Machines_MachineLazyTableRuntime`, `MinUncut_Machines_MachineLookup`, `MinUncut_Machines_MachineOverlayRows`, `MinUncut_Machines_MachineOverlayTable`, `MinUncut_Machines_MachinePaddedExpanderFamilyBounds`, `MinUncut_Machines_MachinePaddedOverlay`, `MinUncut_Machines_MachinePortReindex`, `MinUncut_Machines_MachinePreservingLookup`, `MinUncut_Machines_MachineRegularLift`, `MinUncut_Machines_MachineRegularMetadata`, `MinUncut_Machines_MachineRegularOriginalBody`, `MinUncut_Machines_MachineRegularOwnerProgram`, `MinUncut_Machines_MachineRegularTableRuntime`, `MinUncut_Machines_MachineRegularTableTrace`, `MinUncut_Machines_MachineRegularVertexBlock`, `MinUncut_Machines_PoweringMachineField`, `MinUncut_Machines_PoweringMachineGlobal`, `MinUncut_Machines_PoweringMachineRelation`, `MinUncut_Machines_PoweringMachineRotor`, `MinUncut_Machines_PoweringMachineRow`, `MinUncut_Machines_PoweringMachineRowHeaders`, `MinUncut_Machines_PoweringMachineRuntime`, `MinUncut_Machines_PoweringMachineVertex`, `MinUncut_Machines_PreprocessingMachineBounds`, `MinUncut_Machines_SelectorMachine`, `MinUncut_PCP_ExpanderRowControl`, `MinUncut_PCP_ExpanderTableEnumeration`, `MinUncut_PCP_GraphGap`, `MinUncut_PCP_GraphTables`, `MinUncut_PCP_PortTableLookup`, `MinUncut_PCP_PreprocessingFamilyBridge`, `MinUncut_PCP_PreprocessingInternalRows`, `MinUncut_PCP_PreprocessingLazyWords`, `MinUncut_PCP_PreprocessingOverlayWords`, `MinUncut_PCP_PreprocessingPaddingWords`, `MinUncut_PCP_PreprocessingRegularBounds`, `MinUncut_PCP_PreprocessingRegularTables`, `MinUncut_PCP_PreprocessingStageMaps`.
--
--   **Imports.** It imports the bundles `OAIQ076M014` and `OAIQ076M019` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M028`, `OAIQ076M029` and `OAIQ076M030`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ076M014
import Definitions.Def_OAIQ076M019

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PortTables

open PoweringWalks

variable {n d : Nat}

def tableWords (table : Table n d) : List Nat := GraphTables.tableWords (graphTable table)

def inputBits {ports : Nat} (input : Input ports) : List Bool := tableBits input.2

theorem tableWords_eq (table : Table n d) :
    tableWords table = [n, n * d] ++ (flatRows table).toList.flatMap GraphTables.rowWords := rfl

theorem vertices_le_tableBits_length (table : Table n d) : n ≤ (tableBits table).length :=
  GraphTables.vertices_le_tableBits_length (graphTable table)

end MinUncutGames.Foundations.PCP.PortTables

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_GraphGap
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

theorem overlay_rotation_old {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin d) :
    PortTables.rotation (overlay G H) (v, overlayPorts d e (Sum.inl i)) =
      ((PortTables.rotation G (v, i)).1,
        overlayPorts d e (Sum.inl (PortTables.rotation G (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (Sum.inl i)

theorem overlay_rotation_expander {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin e) :
    PortTables.rotation (overlay G H) (v, overlayPorts d e (Sum.inr i)) =
      ((ExpanderTables.lookup H (v, i)).1,
        overlayPorts d e (Sum.inr (ExpanderTables.lookup H (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (Sum.inr i)

theorem lazy_rotation_false {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) :
    PortTables.rotation (lazy G) (v, lazyPorts d (false, i)) =
      (v, lazyPorts d (false, i)) := by
  exact rotation_materialize_image _ _ v (false, i)

theorem lazy_rotation_true {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) :
    PortTables.rotation (lazy G) (v, lazyPorts d (true, i)) =
      ((PortTables.rotation G (v, i)).1,
        lazyPorts d (true, (PortTables.rotation G (v, i)).2)) := by
  exact rotation_materialize_image _ _ v (true, i)

end MinUncutGames.Foundations.PCP.PreprocessingOverlayTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingRegularTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

theorem relations_pad_new (table : Table n d) (h : n ≤ m)
    (v : Fin (m - n)) (p : Fin d) :
    (pad table h).relations[rowIndex m d (vertexEquiv h (Sum.inr v), p)] =
      Vector.replicate 4096 true := by
  apply relation_ext
  intro a b
  simpa only [PortTables.accepts, GraphTables.relationAt, Fin.getElem_fin,
    Vector.getElem_replicate] using
    accepts_pad_new table h v p a b

end MinUncutGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Input
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLookupSpec

theorem encoded_selected_split (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    encodeWords values = encodeWords (values.take i) ++ encodeWord value ++
      encodeWords (values.drop (i + 1)) := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  have hs : values = values.take i ++ value :: values.drop (i + 1) := by
    calc
      values = values.take i ++ values.drop i := (List.take_append_drop i values).symm
      _ = _ := by rw [List.drop_eq_getElem_cons hi, hv]
  simpa only [encodeWords_append, encodeWords, List.append_assoc] using
    congrArg encodeWords hs

theorem scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    scannedBits values i = (encodeWords (values.take i)).length + value + 1 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, hv⟩
  simp [scannedBits, List.take_succ_eq_append_getElem hi, hv, encodeWords,
    Nat.add_assoc]

theorem selected_scan_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWords (values.take i)).length + value + 1 ≤
      (encodeWords values).length := by
  rw [← scannedBits_of_some values i value h]
  exact scannedBits_le values i

theorem index_length_le (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    (encodeWord i).length ≤ (encodeWords values).length := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  have hp : i ≤ (encodeWords (values.take i)).length := by
    simp only [encodeWords_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
    omega
  have hs := selected_scan_length_le values i value h
  rw [encodeWord_length]
  omega

theorem steps_le_encoded_length_strong (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * i + 2 := by
  induction values generalizing i with
  | nil => simp [steps, encodeWords]
  | cons n ns ih =>
    cases i with
    | zero =>
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega
    | succ i =>
      have ht := ih i
      simp only [steps, encodeWords, List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_lt (values : List Nat) (i : Nat)
    (h : i < values.length) :
    steps values i = scannedBits values i + i + 2 := by
  induction values generalizing i with
  | nil => simp at h
  | cons n ns ih =>
    cases i with
    | zero => simp [steps, scannedBits, encodeWords, Nat.add_assoc]
    | succ i =>
      have ht := ih i (by simpa using h)
      simp only [scannedBits] at ht
      simp only [steps, scannedBits, List.take_succ_cons, encodeWords,
        List.length_append, encodeWord_length]
      omega

theorem steps_eq_scannedBits_of_some (values : List Nat) (i value : Nat)
    (h : values[i]? = some value) :
    steps values i = scannedBits values i + i + 2 := by
  rcases List.getElem?_eq_some_iff.mp h with ⟨hi, _⟩
  exact steps_eq_scannedBits_of_lt values i hi

theorem steps_le_input_encoding_size (values : List Nat) (i : Nat) :
    steps values i ≤ (encodeWords values).length + 2 * (encodeWord i).length := by
  have h := steps_le_encoded_length_strong values i
  rw [encodeWord_length]
  omega

end MinUncutGames.Foundations.Complexity.MachineLookupSpec

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLookup
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLookup

open _root_.Turing
open MachineComposition

variable {K σ : Type} [DecidableEq K]

theorem guard_step_succ (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (i : Nat) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) input output⟩ =
      some ⟨some .skip, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord, List.replicate_succ, update_index]

theorem guard_step_zero (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination)
    (base : K → List Bool) (indexSuffix input output : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (program index source destination)
      ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ =
      some ⟨some .select, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) input output⟩ := by
  change some (TM2.stepAux (program index source destination .guard) _ _) = _
  simp [program, MachineUnaryCounter.guard, TM2.stepAux,
    tapes_index, his, hid, encodeWord]

theorem copyTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 1]
      (some ⟨some .copy, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) (false :: output)⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  have h := Hastad.SourceMachine.fieldLoopTrace source destination hsd
    Label.copy (some Label.accepted) (program index source destination) rfl
    (Function.update base index counter) n suffix (false :: output) ambient register
  simpa only [Hastad.SourceMachine.fieldTapes, tapes, encodeWord,
    List.append_assoc, List.singleton_append] using h

theorem selectTrace (index source destination : K)
    (hsd : source ≠ destination) (base : K → List Bool)
    (counter : List Bool) (n : Nat) (suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .select, (ambient, register), tapes index source destination base
        counter (encodeWord n ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        counter suffix (encodeWord n ++ output)⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [select_step_nonempty index source destination hsd base counter
    (encodeWord n ++ suffix) output (by simp [encodeWord]) ambient register]
  exact copyTrace index source destination hsd base counter n suffix output ambient _

theorem skipCycleTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (i n : Nat) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[n + 2]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord (i + 1) ++ indexSuffix) (encodeWord n ++ suffix) output⟩) =
      some ⟨some .guard, (ambient, none), tapes index source destination base
        (encodeWord i ++ indexSuffix) suffix output⟩ := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  simp only [advance_some]
  rw [guard_step_succ index source destination his hid]
  have h := discardTrace source Label.skip Label.guard
    (program index source destination) rfl
    (tapes index source destination base (encodeWord i ++ indexSuffix)
      (encodeWord n ++ suffix) output) n suffix (by simp [hsd]) ambient none
  simpa only [update_source index source destination hsd] using h

theorem successPrefixTrace (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List Nat) (value : Nat)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[
        (encodeWords prior).length + prior.length + value + 3]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord prior.length ++ indexSuffix)
        (encodeWords prior ++ (encodeWord value ++ suffix)) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) suffix (encodeWord value ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [encodeWords, List.length_nil, Nat.zero_add, List.nil_append]
    rw [show value + 3 = (value + 2) + 1 by omega, Function.iterate_succ_apply]
    simp only [advance_some]
    rw [guard_step_zero index source destination his hid]
    exact selectTrace index source destination hsd base _ value suffix output ambient none
  | cons n prior ih =>
    simp only [encodeWords, List.length_cons, List.length_append, encodeWord_length]
    rw [show n + 1 + (encodeWords prior).length + (prior.length + 1) + value + 3 =
      ((encodeWords prior).length + prior.length + value + 3) + (n + 2) by omega,
      Function.iterate_add_apply]
    rw [List.append_assoc,
      skipCycleTrace index source destination his hid hsd base prior.length n]
    exact ih none

theorem lookupTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value)
    (indexSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program index source destination)))^[MachineLookupSpec.steps values i]
      (some ⟨some .guard, (ambient, register), tapes index source destination base
        (encodeWord i ++ indexSuffix) (encodeWords values ++ suffix) output⟩) =
      some ⟨some .accepted, (ambient, none), tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  have hi := (List.getElem?_eq_some_iff.mp selected).1
  have hlength : (values.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hsource : encodeWords (values.take i) ++
      (encodeWord value ++ (encodeWords (values.drop (i + 1)) ++ suffix)) =
      encodeWords values ++ suffix := by
    rw [MachineLookupSpec.encoded_selected_split values i value selected]
    simp only [List.append_assoc]
  have htime : MachineLookupSpec.steps values i =
      (encodeWords (values.take i)).length + i + value + 3 := by
    rw [MachineLookupSpec.steps_eq_scannedBits_of_some values i value selected,
      MachineLookupSpec.scannedBits_of_some values i value selected]
    omega
  have h := successPrefixTrace index source destination his hid hsd base (values.take i)
    value indexSuffix (encodeWords (values.drop (i + 1)) ++ suffix) output ambient register
  rw [hlength, hsource] at h
  simpa only [htime] using h

end MinUncutGames.Foundations.Complexity.MachineLookup

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Driver
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.PCP.AlphabetTable.Body

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def bodyTime (q N : Nat) : Nat :=
  (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)

end MinUncutGames.Foundations.PCP.AlphabetTable.Body

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteAlphabet
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

open _root_.Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

def bitEncoding (bit : Bool) : List Bool := encodeWord (if bit then 1 else 0)

theorem encodeWord_eq_iff (a b : Nat) : encodeWord a = encodeWord b ↔ a = b := by
  constructor
  · intro h
    have hlength := congrArg List.length h
    simp only [encodeWord_length] at hlength
    omega
  · rintro rfl
    rfl

theorem emit_step (destination : K) (bit : Bool) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (label : Λ) (atEmit : program label = emit destination bit exit)
    (state : State A) (base : K → List Bool) :
    TM2.step program ⟨some label, state, base⟩ =
      some ⟨exit, state,
        Function.update base destination (bitEncoding bit ++ base destination)⟩ := by
  change some (TM2.stepAux (program label) state base) = _
  rw [atEmit]
  cases bit <;> cases exit <;>
    simp [emit, exitAt, TM2.stepAux, bitEncoding, encodeWord, Function.update_idem]

end MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRow
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineRow

open _root_.Turing
open MachineFixedBlockMap
open MinUncutGames.Foundations.PCP

theorem encodeBits_graphWords (bits : List Bool) :
    encodeBits bits = encodeWords (bits.map GraphTables.bitWord) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [encodeBits, encodeBit, encodeWords,
      GraphTables.bitWord, encodeWord, ih]

section Chains

variable {K Λ σ : Type} {N : Nat}

variable [DecidableEq K]

theorem stepAux_readEncodedSlots (src : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readEncodedSlots src slots next) (ambient, buffer)
        (Function.update tapes src (encodeBits (slots.map bits) ++ suffix)) =
      TM2.stepAux next (ambient, fill slots bits buffer)
        (Function.update tapes src suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readEncodedSlots, encodeBits, fill]
  | cons i slots ih =>
      cases hb : bits i <;>
        simpa only [readEncodedSlots, List.map_cons, encodeBits, encodeBit, hb,
          Bool.false_eq_true, ite_false, ite_true, List.cons_append,
          List.nil_append, TM2.stepAux, Function.update_self, List.head?_cons,
          Option.getD_some, List.tail_cons, Function.update_idem, Bool.cond_false,
          Bool.cond_true, fill, List.foldl_cons] using
          ih (Function.update buffer i (bits i)) tapes

theorem stepAux_readEncodedAll (src : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (readEncodedSlots src (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes src suffix) := by
  have h := stepAux_readEncodedSlots src (List.ofFn id) next
    state.1 bits state.2 tapes suffix
  have hin : Function.update tapes src
      (encodeBits ((List.ofFn id).map bits) ++ suffix) = tapes := by
    simpa only [List.map_ofFn, Function.comp_id, ← hinput] using
      Function.update_eq_self src tapes
  rw [hin, fill_all] at h
  exact h

theorem stepAux_writeEncodedSlots {M : Nat} (dst : K) (emit : σ → Buffer M)
    (slots : List (Fin M)) (next : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (writeEncodedSlots dst emit slots next) state tapes =
      TM2.stepAux next state
        (Function.update tapes dst
          (encodeBits ((slots.map (emit state)).reverse) ++ tapes dst)) := by
  induction slots generalizing tapes with
  | nil => simp [writeEncodedSlots, encodeBits]
  | cons i slots ih =>
      cases hb : emit state i <;>
        simp only [writeEncodedSlots, TM2.stepAux, hb, Bool.cond_false, Bool.cond_true]
      all_goals rw [ih]
      all_goals simp [Function.update_idem, List.map_cons, List.reverse_cons,
        encodeBits_append, encodeBits, encodeBit, hb, List.append_assoc]

end Chains

section Block

variable {K Λ σ : Type} {N M : Nat}

variable [DecidableEq K]

theorem stepAux_encodedBlockStmt (src dst : K) (F : Buffer N → Buffer M)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockStmt src dst F next) state tapes =
      TM2.stepAux next (state.1, emptyBuffer N)
        (Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst)) := by
  unfold encodedBlockStmt
  rw [stepAux_readEncodedAll src _ state bits tapes suffix hinput,
    stepAux_writeEncodedSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]

theorem stepAux_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : σ × Buffer N) (tapes : K → List Bool)
    (hinput : tapes src = encodeBits (List.ofFn bits) ++ suffix) :
    TM2.stepAux (encodedBlockAt src dst F exit) state tapes =
      { l := exit, var := (state.1, emptyBuffer N),
        stk := Function.update (Function.update tapes src suffix) dst
          (encodeBits (List.ofFn (F bits)) ++ tapes dst) } := by
  rw [encodedBlockAt, stepAux_encodedBlockStmt src dst F _ hne bits suffix state tapes hinput]
  cases exit <;> rfl

end Block

end MinUncutGames.Foundations.Complexity.PoweringMachineRow

end
section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineLoop

open _root_.Turing

def initialTapes (n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord n ++ suffix
  | _ => []

def scanConfiguration {σ : Type} (B remaining processed : Nat)
    (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨some .scan, (ambient, register), scanTapes B remaining processed suffix⟩

def finalConfiguration {σ : Type} (B n : Nat) (suffix : List Bool) (ambient : σ) :
    TM2.Cfg HeaderAlphabet HeaderLabel (HeaderState σ) :=
  ⟨none, (ambient, none), finalTapes B n suffix⟩

theorem initializeStep {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩ =
        some (scanConfiguration B n 0 suffix ambient none) := by
  simp only [TM2.step, headerProgram, TM2.stepAux]
  congr 2
  funext tape
  cases tape <;> simp [initialTapes, scanTapes, encodeWord]

theorem scanStep_zero {σ : Type} (B processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B) (scanConfiguration B 0 processed suffix ambient register) =
      some (finalConfiguration B processed suffix ambient) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_false]
  congr 2
  funext tape
  cases tape <;> simp [finalTapes, scanTapes]

theorem scanStep_succ {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step (headerProgram B)
      (scanConfiguration B (remaining + 1) processed suffix ambient register) =
      some (scanConfiguration B remaining (processed + 1) suffix ambient none) := by
  simp only [TM2.step, scanConfiguration, headerProgram, TM2.stepAux,
    scanTapes, encodeWord, List.replicate_succ, List.cons_append,
    List.head?_cons, List.tail_cons, Option.getD_some, Bool.cond_true]
  rw [stepAux_pushTrue]
  simp only [TM2.stepAux]
  congr 2
  funext tape
  cases tape <;>
    simp [scanTapes, encodeWord, Nat.mul_add, List.replicate_add,
      List.replicate_succ, List.append_assoc, Nat.add_comm,
      -List.replicate_append_replicate]

theorem scanTrace {σ : Type} (B remaining processed : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (some (scanConfiguration B remaining processed suffix ambient register)) =
      some (finalConfiguration B (processed + remaining) suffix ambient) := by
  induction remaining generalizing processed register with
  | zero =>
    simpa only [Nat.add_zero, Nat.zero_add, Function.iterate_one, MachineComposition.advance_some] using
      scanStep_zero B processed suffix ambient register
  | succ remaining ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step (headerProgram B)))^[remaining + 1]
      (TM2.step (headerProgram B)
        (scanConfiguration B (remaining + 1) processed suffix ambient register)) = _
    rw [scanStep_succ, ih]
    simp only [Nat.add_comm, Nat.add_left_comm]

theorem headerTrace {σ : Type} (B n : Nat) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 2]
      (some ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩) =
      some (finalConfiguration B n suffix ambient) := by
  rw [show n + 2 = (n + 1) + 1 by omega, Function.iterate_succ_apply]
  change (MachineComposition.advance (TM2.step (headerProgram B)))^[n + 1]
    (TM2.step (headerProgram B)
      ⟨some .initialize_, (ambient, register), initialTapes n suffix⟩) = _
  rw [initializeStep]
  simpa only [Nat.zero_add] using scanTrace B n 0 suffix ambient none

end MinUncutGames.Foundations.Complexity.PoweringMachineLoop

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachinePreservingLookup
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachinePreservingLookup

open _root_.Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat)
    (indexSuffix workSuffix output : List Bool) : K → List Bool :=
  MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
    (encodeWord 0 ++ indexSuffix)
    (encodeWords (values.drop (index + 1)) ++ workSuffix) (encodeWord value ++ output)

theorem lookupFramedHaltTrace_some (index source destination : K)
    (his : index ≠ source) (hid : index ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) (indexSuffix suffix output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (MachineLookup.program index source destination)))^[
      MachineLookupSpec.steps values i + 1]
      (some ⟨some MachineLookup.Label.guard, (ambient,register),
        MachineLookup.tapes index source destination base (encodeWord i ++ indexSuffix)
          (encodeWords values ++ suffix) output⟩) =
      some ⟨none, (ambient,none), MachineLookup.tapes index source destination base
        (encodeWord 0 ++ indexSuffix) (encodeWords (values.drop (i + 1)) ++ suffix)
        (encodeWord value ++ output)⟩ := by
  rw [Function.iterate_succ_apply',
    MachineLookup.lookupTrace_some index source destination his hid hsd
      base values i value selected indexSuffix suffix output ambient register]
  simp only [advance_some, TM2.step, MachineLookup.program, TM2.stepAux]

theorem preservingLookupTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (firstLabel secondLabel : Λ) (lookupLabels : MachineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atFirst : program firstLabel = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 4) id false firstLabel (some secondLabel))
    (atSecond : program secondLabel = MachineCopy.forkLoop
      (tape 4) (tape 0) (tape 2) false secondLabel (some (lookupLabels .guard)))
    (atLookup : ∀ l, program (lookupLabels l) =
      MachineSubroutine.statement lookupLabels exit (MachineLookup.program (tape 1) (tape 2) (tape 3) l))
    (base : K → List Bool) (values : List Nat) (tableWord : base (tape 0) = encodeWords values)
    (scratchEmpty : base (tape 4) = []) (i value : Nat) (selected : values[i]? = some value)
    (indexSuffix workSuffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[
      2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1]
      (some ⟨some firstLabel, (ambient,register),
        initialTapes tape base i indexSuffix workSuffix output⟩) =
      some ⟨exit, (ambient,none), finalTapes tape base values i value indexSuffix workSuffix output⟩ := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  let start := initialTapes tape base i indexSuffix workSuffix output
  have htable : start (tape 0) = encodeWords values := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 0 1 (by decide)) (hd 0 2 (by decide)) (hd 0 3 (by decide))] using tableWord
  have hs : start (tape 4) = [] := by
    simpa only [start, initialTapes, MachineLookup.tapes_other _ _ _ _
      (hd 4 1 (by decide)) (hd 4 2 (by decide)) (hd 4 3 (by decide))] using scratchEmpty
  have hwork : start (tape 2) = workSuffix := by
    simp only [start, initialTapes, MachineLookup.tapes_source _ _ _ (hd 2 3 (by decide))]
  have hcopy := MachineCopy.copyTrace (tape 0) (tape 2) (tape 4)
    (hd 0 2 (by decide)) (hd 0 4 (by decide)) (hd 2 4 (by decide)) false
    firstLabel secondLabel (some (lookupLabels .guard)) program atFirst atSecond start hs ambient register
  rw [htable, hwork] at hcopy
  simp only [start, initialTapes, MachineLookup.update_source _ _ _ (hd 2 3 (by decide))] at hcopy
  have hlookup := MachineSubroutine.trace lookupLabels exit
    (MachineLookup.program (tape 1) (tape 2) (tape 3)) program atLookup
    (MachineLookupSpec.steps values i + 1) _ _
    (lookupFramedHaltTrace_some (tape 1) (tape 2) (tape 3)
      (hd 1 2 (by decide)) (hd 1 3 (by decide)) (hd 2 3 (by decide))
      base values i value selected indexSuffix workSuffix output ambient none)
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at hlookup
  rw [show 2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 =
      (MachineLookupSpec.steps values i + 1) + 2 * ((encodeWords values).length + 1) by omega,
    Function.iterate_add_apply]
  change (advance (TM2.step program))^[MachineLookupSpec.steps values i + 1]
    ((advance (TM2.step program))^[2 * ((encodeWords values).length + 1)]
      (some ⟨some firstLabel, (ambient,register),
        MachineLookup.tapes (tape 1) (tape 2) (tape 3) base
          (encodeWord i ++ indexSuffix) workSuffix output⟩)) = _
  rw [hcopy]
  exact hlookup

theorem preservingLookup_steps_le (values : List Nat) (i value : Nat)
    (selected : values[i]? = some value) :
    2 * ((encodeWords values).length + 1) + MachineLookupSpec.steps values i + 1 ≤
      5 * (encodeWords values).length + 3 := by
  have ht := MachineLookupSpec.steps_le_input_encoding_size values i
  have hi := MachineLookupSpec.index_length_le values i value selected
  omega

end MinUncutGames.Foundations.Complexity.MachinePreservingLookup

namespace MinUncutGames.Foundations.Complexity.MachineAffineLookup

open _root_.Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def finalTapes (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) : K → List Bool :=
  MachinePreservingLookup.finalTapes tape base values index value
    (base (tape 1)) (base (tape 2)) (base (tape 3))

theorem initialTapes_eq_update (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (i : Nat) :
    MachinePreservingLookup.initialTapes tape base i
      (base (tape 1)) (base (tape 2)) (base (tape 3)) =
      Function.update base (tape 1) (encodeWord i ++ base (tape 1)) := by
  have hd (a b : Fin 5) (hne : a ≠ b) : tape a ≠ tape b := fun h => hne (distinct h)
  funext k
  by_cases h₁ : k = tape 1
  · subst k
    simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
      hd 1 2 (by decide), hd 1 3 (by decide)]
  · by_cases h₂ : k = tape 2
    · subst k
      simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁,
        hd 2 3 (by decide)]
    · by_cases h₃ : k = tape 3
      · subst k
        simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁]
      · simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes, h₁, h₂, h₃]

theorem finalTapes_other (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) (k : K)
    (h₁ : k ≠ tape 1) (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) :
    finalTapes tape base values index value k = base k :=
  MachineLookup.tapes_other _ _ _ _ h₁ h₂ h₃ _ _ _ _

theorem finalTapes_output (tape : Fin 5 → K) (base : K → List Bool)
    (values : List Nat) (index value : Nat) :
    finalTapes tape base values index value (tape 3) = encodeWord value ++ base (tape 3) :=
  MachineLookup.tapes_destination _ _ _ _ _ _ _

end MinUncutGames.Foundations.Complexity.MachineAffineLookup

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PortTableLookup
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PortTableLookup

variable {n d : Nat}

theorem row_word (table : PortTables.Table n d) (i : Fin (n * d))
    (j : Nat) (hj : j < 4098) :
    (PortTables.tableWords table)[2 + 4098 * i.val + j]? =
      (GraphTables.rowWords (PortTables.flatRows table)[i])[j]? := by
  rw [PortTables.tableWords_eq]
  change (n :: n * d :: (PortTables.flatRows table).toList.flatMap
    GraphTables.rowWords)[2 + 4098 * i.val + j]? = _
  rw [show 2 + 4098 * i.val + j = (4098 * i.val + j + 1) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_cons_succ]
  apply flatMap_word GraphTables.rowWords 4098 j hj
    (PortTables.flatRows table).toList
    (fun row _ => GraphTables.rowWords_length row) i.val
    ((PortTables.flatRows table)[i])
  simp only [Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt,
    Fin.getElem_fin]

end MinUncutGames.Foundations.PCP.PortTableLookup

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRotor
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRotor

open _root_.Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def reverseId (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  table.reverseIndex[PortTables.rowIndex n d (vertex, port)].val

def endpointAddress (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) : Nat :=
  4098 * reverseId table vertex port + 2

def afterReverse (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (reverseTapes tape) base (PortTables.tableWords table)
    (reverseAddress vertex port) (reverseId table vertex port)

def finalTapes (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (endpointTapes tape)
    (afterReverse tape table vertex port base) (PortTables.tableWords table)
    (endpointAddress table vertex port) ((PortTables.rotation table (vertex, port)).1.val)

theorem finalTapes_endpoint (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d) (base : K → List Bool) :
    finalTapes tape table vertex port base (tape 5) =
      encodeWord ((PortTables.rotation table (vertex, port)).1.val) ++ base (tape 5) := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change MachineAffineLookup.finalTapes (endpointTapes tape) _ _ _ _ (endpointTapes tape 3) = _
  rw [MachineAffineLookup.finalTapes_output]
  congr 1
  exact MachineAffineLookup.finalTapes_other _ _ _ _ _ _
    (hd 5 2 (by decide)) (hd 5 3 (by decide)) (hd 5 4 (by decide))

theorem finalTapes_other (tape : Fin 7 → K) (table : PortTables.Table n d)
    (vertex : Fin n) (port : Fin d) (base : K → List Bool) (k : K)
    (h₂ : k ≠ tape 2) (h₃ : k ≠ tape 3) (h₄ : k ≠ tape 4) (h₅ : k ≠ tape 5) :
    finalTapes tape table vertex port base k = base k := by
  calc
    finalTapes tape table vertex port base k = afterReverse tape table vertex port base k :=
      MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h₂ h₃ h₅
    _ = base k := MachineAffineLookup.finalTapes_other _ _ _ _ _ _ h₂ h₃ h₄

end MinUncutGames.Foundations.Complexity.PoweringMachineRotor

namespace MinUncutGames.Foundations.Complexity.PoweringMachineWord

open _root_.Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def finalTapes (table : PortTables.Table n d) :
    (t : Nat) → (Tape t → K) → Fin n → (Fin t → Fin d) → (K → List Bool) → K → List Bool
  | 0, placement, vertex, _, base =>
      Function.update base (placement (.inl 5)) (encodeWord vertex.val ++ base (placement (.inl 5)))
  | t + 1, placement, vertex, ports, base =>
      finalTapes table t (placement ∘ shift t) (PortTables.rotation table (vertex, ports 0)).1
        (fun j => ports j.succ)
        (PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base)

theorem finalTapes_other (table : PortTables.Table n d) (t : Nat)
    (placement : Tape t → K) (vertex : Fin n) (ports : Fin t → Fin d)
    (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 1)) (hscan : k ≠ placement (.inl 2))
    (hreverse : k ≠ placement (.inl 3)) (houtput : k ≠ placement (.inl 5))
    (hpositions : ∀ i : Fin t, k ≠ placement (.inr i.succ)) :
    finalTapes table t placement vertex ports base k = base k := by
  induction t generalizing vertex base with
  | zero => simp only [finalTapes, Function.update_of_ne houtput]
  | succ t ih =>
      let mid := PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base
      calc
        finalTapes table (t + 1) placement vertex ports base k = mid k :=
          ih (placement ∘ shift t) (PortTables.rotation table (vertex, ports 0)).1
            (fun j => ports j.succ) mid hquery hscan hreverse houtput
            (fun i => hpositions i.succ)
        _ = base k := PoweringMachineRotor.finalTapes_other _ _ _ _ _ k
          hquery hscan hreverse (hpositions (first t))

end MinUncutGames.Foundations.Complexity.PoweringMachineWord

namespace MinUncutGames.Foundations.Complexity.PoweringMachineInitialize

open _root_.Turing
open PoweringMachineLoop PoweringMasterState

def headerConfiguration {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    TM2.Cfg (fun _ : GlobalTape max => Bool) Label (Master N) :=
  ⟨c.l.map Sum.inl, c.var, mergeTapes c.stk extra⟩

theorem headerConfiguration_eq {max N : Nat} (extra : ExtraTape max → List Bool)
    (c : TM2.Cfg HeaderAlphabet HeaderLabel (Master N)) :
    headerConfiguration extra c =
      MachineStateEquiv.configuration (dropUnit N)
        (castConfiguration (boolAlphabet_eq max)
          (MachineEmbedding.configuration (Λextra := MachineUnaryAffineAt.Label)
            none () extra c)) := by
  cases c with
  | mk label state tapes =>
    simp only [MachineEmbedding.configuration, castConfiguration_mk,
      MachineStateEquiv.configuration, castTapes_embedding, dropUnit,
      Equiv.coe_fn_mk, headerConfiguration]
    cases label <;> rfl

theorem stepAux_headerStatement (max N B : Nat) (label : HeaderLabel)
    (state : Master N) (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    TM2.stepAux (headerStatement max N B label) state (mergeTapes header extra) =
      headerConfiguration extra (TM2.stepAux (headerProgram B label) state header) := by
  rw [headerStatement, MachineStateEquiv.stepAux_transport_symm]
  change MachineStateEquiv.configuration (dropUnit N)
    (TM2.stepAux (castStatement (boolAlphabet_eq max)
      (MachineEmbedding.statement none (headerProgram B label))) (state, ())
      (mergeTapes header extra)) = _
  rw [← castTapes_embedding, stepAux_cast, MachineEmbedding.stepAux_simulation]
  exact (headerConfiguration_eq extra _).symm

theorem headerStep (max N B : Nat) (extra : ExtraTape max → List Bool)
    (a b : TM2.Cfg HeaderAlphabet HeaderLabel (Master N))
    (run : TM2.step (headerProgram B) a = some b) :
    TM2.step (program max N B) (headerConfiguration extra a) =
      some (headerConfiguration extra b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => simp [TM2.step] at run
    | some label =>
      have hb : TM2.stepAux (headerProgram B label) state tapes = b := Option.some.inj run
      rw [← hb]
      change some (TM2.stepAux (headerStatement max N B label) state
        (mergeTapes tapes extra)) = _
      rw [stepAux_headerStatement]

theorem headerTrace (max N B vertices : Nat) (extra : ExtraTape max → List Bool)
    (state : Master N) :
    (MachineComposition.advance (TM2.step (program max N B)))^[vertices + 2]
      (some ⟨some (.inl .initialize_), state,
        mergeTapes (initialTapes vertices []) extra⟩) =
      some ⟨none, (state.1, none), mergeTapes (finalTapes B vertices []) extra⟩ := by
  exact MachineComposition.liftSuccessfulTrace (TM2.step (headerProgram B))
    (TM2.step (program max N B)) (headerConfiguration extra)
    (headerStep max N B extra) (vertices + 2) _ _
    (PoweringMachineLoop.headerTrace B vertices [] state.1 state.2)

end MinUncutGames.Foundations.Complexity.PoweringMachineInitialize

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRelation
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRelation

open _root_.Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def value (table : PortTables.Table n d) (vertex : Fin n) (port : Fin d)
    (position : Fin 4096) : Nat :=
  GraphTables.bitWord table.relations[PortTables.rowIndex n d (vertex, port)][position]

end MinUncutGames.Foundations.Complexity.PoweringMachineRelation

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRelationField

open _root_.Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

def endpoint (table : PortTables.Table n d) (vertex : Fin n) (path : List (Fin d)) : Fin n :=
  PoweringWalks.walkEnd (PortTables.portGraph table) vertex path

def bit (table : PortTables.Table n d) (vertex : Fin n) (path : List (Fin d))
    (port : Fin d) (left right : PortTables.Label) : Nat :=
  GraphTables.bitWord (PortTables.accepts table (endpoint table vertex path, port) left right)

def afterWord (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (table : PortTables.Table n d)
    (vertex : Fin n) (base : K → List Bool) : K → List Bool :=
  PoweringMachineWord.finalTapes table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    vertex path.get base

def finalTapes (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool) : K → List Bool :=
  MachineAffineLookup.finalTapes (lookupTapes placement)
    (afterWord placement path lengthBound table vertex base) (PortTables.tableWords table)
    (PoweringMachineRelation.address (endpoint table vertex path) port
      (GraphTables.relationIndex (left, right))) (bit table vertex path port left right)

theorem afterWord_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4) (h₆ : role ≠ 6) :
    afterWord placement path lengthBound table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  apply PoweringMachineWord.finalTapes_other
  · intro h; exact h₂ (by simpa [PoweringMachineTapes.query] using distinct h)
  · intro h; exact h₃ (by simpa [PoweringMachineTapes.scan] using distinct h)
  · intro h; exact h₄ (by simpa [PoweringMachineTapes.reverse] using distinct h)
  · intro h; exact h₆ (by simpa [PoweringMachineTapes.leftEndpoint] using distinct h)
  · intro i h
    have heq := distinct h
    simp at heq

theorem finalTapes_frame (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (role : Fin 11) (h₂ : role ≠ 2) (h₃ : role ≠ 3) (h₄ : role ≠ 4)
    (h₆ : role ≠ 6) (h₁₀ : role ≠ 10) :
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
      base (placement (.inl role)) := by
  calc
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl role)) =
        afterWord placement path lengthBound table vertex base (placement (.inl role)) := by
      apply MachineAffineLookup.finalTapes_other
      · intro h; exact h₂ (by simpa [lookupTapes, PoweringMachineTapes.query] using distinct h)
      · intro h; exact h₃ (by simpa [lookupTapes, PoweringMachineTapes.scan] using distinct h)
      · intro h; exact h₁₀ (by simpa [lookupTapes, PoweringMachineTapes.rowOutput] using distinct h)
    _ = _ := afterWord_frame placement distinct path lengthBound table vertex base role h₂ h₃ h₄ h₆

end MinUncutGames.Foundations.Complexity.PoweringMachineRelationField

namespace MinUncutGames.Foundations.Complexity.PoweringMachineEqualityField

open _root_.Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

def endpoint (graph : PortTables.Table n d) {t : Nat} (vertex : Fin n)
    (ports : Fin t → Fin d) : Fin n :=
  PoweringWalks.wordEnd (PortTables.portGraph graph) t vertex ports

def resultBit (graph : PortTables.Table n d) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) : Bool :=
  decide (endpoint graph vertex left = endpoint graph vertex right)

def wordTapes (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (target : Bool) (vertex : Fin n)
    (ports : Fin t → Fin d) (base : K → List Bool) : K → List Bool :=
  PoweringMachineWord.finalTapes graph t
    (placement ∘ PoweringMachineTapes.wordPlacement h target) vertex ports base

def finalTapes (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool) :
    K → List Bool :=
  let afterLeft := wordTapes graph hl placement false vertex left base
  let afterBoth := wordTapes graph hr placement true vertex right afterLeft
  Function.update afterBoth (placement (.inl 10))
    (MachineUnaryEqualityBit.bitEncoding (resultBit graph vertex left right) ++
      afterBoth (placement (.inl 10)))

theorem wordTapes_other (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (target : Bool) (vertex : Fin n)
    (ports : Fin t → Fin d) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 2)) (hscan : k ≠ placement (.inl 3))
    (hreverse : k ≠ placement (.inl 4))
    (houtput : k ≠ placement (PoweringMachineTapes.endpoint max target))
    (hpositions : ∀ i : Fin max, k ≠ placement (.inr i)) :
    wordTapes graph h placement target vertex ports base k = base k := by
  apply PoweringMachineWord.finalTapes_other
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_one,
      PoweringMachineTapes.query] using hquery
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_two,
      PoweringMachineTapes.scan] using hscan
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_three,
      PoweringMachineTapes.reverse] using hreverse
  · simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five] using houtput
  · intro i
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_succ] using
      hpositions (Fin.castLE h i)

theorem wordTapes_role (graph : PortTables.Table n d) {t : Nat} (h : t ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (target : Bool) (vertex : Fin n) (ports : Fin t → Fin d)
    (base : K → List Bool) (j : Fin 11)
    (hquery : j ≠ 2) (hscan : j ≠ 3) (hreverse : j ≠ 4)
    (houtput : j ≠ if target then 7 else 6) :
    wordTapes graph h placement target vertex ports base (placement (.inl j)) =
      base (placement (.inl j)) := by
  apply wordTapes_other
  · intro he
    exact hquery (Sum.inl.inj (distinct he))
  · intro he
    exact hscan (Sum.inl.inj (distinct he))
  · intro he
    exact hreverse (Sum.inl.inj (distinct he))
  · intro he
    apply houtput
    cases target <;> exact Sum.inl.inj (distinct he)
  · intro i he
    cases distinct he

theorem finalTapes_other (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (.inl 2)) (hscan : k ≠ placement (.inl 3))
    (hreverse : k ≠ placement (.inl 4)) (hleft : k ≠ placement (.inl 6))
    (hright : k ≠ placement (.inl 7)) (hrow : k ≠ placement (.inl 10))
    (hpositions : ∀ i : Fin max, k ≠ placement (.inr i)) :
    finalTapes graph hl hr placement vertex left right base k = base k := by
  unfold finalTapes
  rw [Function.update_of_ne hrow]
  rw [wordTapes_other graph hr placement true vertex right _ k
    hquery hscan hreverse hright hpositions]
  exact wordTapes_other graph hl placement false vertex left base k
    hquery hscan hreverse hleft hpositions

theorem finalTapes_role (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement) (vertex : Fin n)
    (left : Fin l → Fin d) (right : Fin r → Fin d) (base : K → List Bool)
    (j : Fin 11) (hrole : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 8 ∨ j = 9) :
    finalTapes graph hl hr placement vertex left right base (placement (.inl j)) =
      base (placement (.inl j)) := by
  apply finalTapes_other
  all_goals first
    | (intro he; have hij := Sum.inl.inj (distinct he); rcases hrole with rfl | rfl | rfl | rfl | rfl <;> simp at hij)
    | (intro i he; cases distinct he)

end MinUncutGames.Foundations.Complexity.PoweringMachineEqualityField

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineField
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineField

open _root_.Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

def finalTapes (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) : (op : Instruction d) → op.radius ≤ max →
      (K → List Bool) → K → List Bool
  | .relation path port a b, bounded, base =>
      PoweringMachineRelationField.finalTapes placement path bounded port a b graph vertex base
  | .equal left right, bounded, base =>
      PoweringMachineEqualityField.finalTapes graph
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement vertex left.get right.get base

structure Ready (graph : PortTables.Table n d) (placement : Tape max → K)
    (vertex : Fin n) (suffix : List Bool) (tapes : K → List Bool) : Prop where
  table : tapes (placement (.inl 0)) = PortTables.tableBits graph
  source : tapes (placement (.inl 1)) = encodeWord vertex.val ++ suffix
  scratch : tapes (placement (.inl 5)) = []
  leftCopy : tapes (placement (.inl 8)) = []
  rightCopy : tapes (placement (.inl 9)) = []

theorem finalTapes_role (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (j : Fin 11) (role : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 8 ∨ j = 9) :
    finalTapes graph placement vertex op bounded base (placement (.inl j)) =
      base (placement (.inl j)) := by
  cases op with
  | relation path port a b =>
      apply PoweringMachineRelationField.finalTapes_frame placement distinct path bounded
        port a b graph vertex base j
      all_goals rcases role with rfl | rfl | rfl | rfl | rfl <;> decide
  | equal left right =>
      exact PoweringMachineEqualityField.finalTapes_role graph _ _ placement distinct
        vertex left.get right.get base j role

theorem ready_finalTapes (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph placement vertex suffix base) :
    Ready graph placement vertex suffix (finalTapes graph placement vertex op bounded base) := by
  constructor
  · rw [finalTapes_role graph placement distinct vertex op bounded base 0 (by simp)]
    exact ready.table
  · rw [finalTapes_role graph placement distinct vertex op bounded base 1 (by simp)]
    exact ready.source
  · rw [finalTapes_role graph placement distinct vertex op bounded base 5 (by simp)]
    exact ready.scratch
  · rw [finalTapes_role graph placement distinct vertex op bounded base 8 (by simp)]
    exact ready.leftCopy
  · rw [finalTapes_role graph placement distinct vertex op bounded base 9 (by simp)]
    exact ready.rightCopy

end MinUncutGames.Foundations.Complexity.PoweringMachineField

namespace MinUncutGames.Foundations.Complexity.PoweringMachinePlan

open _root_.Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

def result (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (op : Command d max) (base : K → List Bool) : K → List Bool :=
  PoweringMachineField.finalTapes graph placement vertex op.val op.property base

def finalTapes (graph : PortTables.Table vertices d) (placement : PoweringMachineTapes.Tape max → K)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool) : K → List Bool :=
  MachineFiniteSequence.resultOf (result graph placement vertex) commands base

theorem ready_finalTapes (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    PoweringMachineField.Ready graph placement vertex suffix
      (finalTapes graph placement vertex commands base) := by
  induction commands generalizing base with
  | nil => exact ready
  | cons op commands ih =>
      apply ih
      exact PoweringMachineField.ready_finalTapes graph placement distinct vertex op.val
        op.property base suffix ready

end MinUncutGames.Foundations.Complexity.PoweringMachinePlan

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_PoweringPlanBudget
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringPlanBudget

open _root_.Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}


def rowBudget (d n inputLength : Nat) : Nat :=
  PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
    fieldBudget (2 * (n + 1)) inputLength

end MinUncutGames.Foundations.Complexity.PoweringPlanBudget

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRowHeaders
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRowHeaders

open _root_.Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

def afterReverse (n : Nat) (placement : Tape max → K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  Function.update base (placement (rowOutput max))
    (encodeWord (reverseValue d n vertex ports direction) ++ base (placement (rowOutput max)))

def finalTapes (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterReverse n placement vertex ports direction base
  if direction then
    PoweringMachineWord.finalTapes input (n + 1) (placement ∘ headerPlacement h) vertex ports mid
  else Function.update mid (placement (rowOutput max))
    (encodeWord vertex.val ++ mid (placement (rowOutput max)))

theorem finalTapes_other (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (k : K)
    (hquery : k ≠ placement (query max)) (hscan : k ≠ placement (scan max))
    (hreverse : k ≠ placement (reverse max)) (houtput : k ≠ placement (rowOutput max))
    (hpositions : ∀ i : Fin (n + 1), k ≠ placement (.inr (Fin.castLE h i))) :
    finalTapes input n h placement vertex ports direction base k = base k := by
  cases direction with
  | false => simp only [finalTapes, Bool.false_eq_true, ite_false,
      Function.update_of_ne houtput, afterReverse]
  | true =>
    let mid := afterReverse n placement vertex ports true base
    have hw := PoweringMachineWord.finalTapes_other input (n + 1)
      (placement ∘ headerPlacement h) vertex ports mid k
      (by simpa only [Function.comp_apply, headerPlacement_query] using hquery)
      (by simpa only [Function.comp_apply, headerPlacement_scan] using hscan)
      (by simpa only [Function.comp_apply, headerPlacement_reverse] using hreverse)
      (by simpa only [Function.comp_apply, headerPlacement_output] using houtput)
      (fun i => by simpa only [Function.comp_apply, headerPlacement_succ] using hpositions i)
    calc
      _ = mid k := hw
      _ = base k := by simp only [mid, afterReverse, Function.update_of_ne houtput]

theorem finalTapes_shared (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d)
    (direction : Bool) (base : K → List Bool) (i : Fin 11)
    (hquery : i ≠ 2) (hscan : i ≠ 3) (hreverse : i ≠ 4) (houtput : i ≠ 10) :
    finalTapes input n h placement vertex ports direction base (placement (.inl i)) =
      base (placement (.inl i)) := by
  apply finalTapes_other input n h placement vertex ports direction base
  · intro heq; exact hquery (Sum.inl.inj (distinct heq))
  · intro heq; exact hscan (Sum.inl.inj (distinct heq))
  · intro heq; exact hreverse (Sum.inl.inj (distinct heq))
  · intro heq; exact houtput (Sum.inl.inj (distinct heq))
  · intro j heq; cases distinct heq

end MinUncutGames.Foundations.Complexity.PoweringMachineRowHeaders

namespace MinUncutGames.Foundations.Complexity.PoweringMachineRowBody

open _root_.Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

omit [DecidableEq K] in
theorem headerPlacement_injective {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    Function.Injective (headerPlacement placement output) := by
  intro i j h
  by_cases hi : i = .inl 10
  · subst i
    by_cases hj : j = .inl 10
    · exact hj.symm
    · exact False.elim (outside j (by simpa [headerPlacement, hj] using h))
  · by_cases hj : j = .inl 10
    · subst j
      exact False.elim (outside i (by simpa [headerPlacement, hi] using h.symm))
    · exact distinct (by simpa [headerPlacement, hi, hj] using h)

omit [DecidableEq K] in
theorem headerPlacement_excludes_data {max : Nat}
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) :
    ∀ i, placement (.inl 10) ≠ headerPlacement placement output i := by
  intro i h
  by_cases hi : i = .inl 10
  · subst i
    exact outside _ (by simpa only [headerPlacement_output] using h.symm)
  · have heq : (.inl 10 : PoweringMachineTapes.Tape max) = i :=
      distinct (by simpa [headerPlacement, hi] using h)
    exact hi heq.symm

def afterPlan (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  PoweringMachinePlan.finalTapes graph placement vertex (commands n ports direction) base

def rowRelation (graph : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : List Bool :=
  encodeWords (GenericGraphTables.relationWords (PoweringTables.table graph n).rows[
    PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports)].relation)

def afterEmit (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) : K → List Bool :=
  let mid := afterPlan graph n placement vertex ports direction base
  Function.update (Function.update mid (placement (.inl 10)) []) output
    (rowRelation graph n vertex ports direction ++ mid output)

def finalTapes (graph : PortTables.Table vertices d)
    (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (base : K → List Bool) : K → List Bool :=
  PoweringMachineRowHeaders.finalTapes graph n (by unfold capacity; omega)
    (headerPlacement placement output) vertex ports direction
    (afterEmit graph n placement output vertex ports direction base)

def Ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (vertex : Fin vertices)
    (suffix : List Bool) (base : K → List Bool) : Prop :=
  PoweringMachineField.Ready graph placement vertex suffix base ∧ base (placement (.inl 10)) = []

theorem afterEmit_data (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (output : K)
    (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) :
    afterEmit graph n placement output vertex ports direction base (placement (.inl 10)) = [] := by
  simp only [afterEmit, Function.update_of_ne (Ne.symm (outside _)), Function.update_self]

theorem afterEmit_role (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (j : Fin 11) (hj : j ≠ 10) :
    afterEmit graph n placement output vertex ports direction base (placement (.inl j)) =
      afterPlan graph n placement vertex ports direction base (placement (.inl j)) := by
  have hdata : placement (.inl j) ≠ placement (.inl 10) := fun h => hj (Sum.inl.inj (distinct h))
  simp only [afterEmit, Function.update_of_ne (Ne.symm (outside _)), Function.update_of_ne hdata]

theorem afterEmit_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    Ready graph n placement vertex suffix (afterEmit graph n placement output vertex ports direction base) := by
  have hp := PoweringMachinePlan.ready_finalTapes graph placement distinct vertex
    (commands n ports direction) base suffix ready.1
  constructor
  · constructor
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 0 (by decide)]
      exact hp.table
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 1 (by decide)]
      exact hp.source
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 5 (by decide)]
      exact hp.scratch
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 8 (by decide)]
      exact hp.leftCopy
    · rw [afterEmit_role graph n placement distinct output outside vertex ports direction base 9 (by decide)]
      exact hp.rightCopy
  · exact afterEmit_data graph n placement output outside vertex ports direction base

theorem finalTapes_data (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool) :
    finalTapes graph n placement output vertex ports direction base (placement (.inl 10)) = [] := by
  have hother := headerPlacement_excludes_data placement distinct output outside
  calc
    finalTapes graph n placement output vertex ports direction base (placement (.inl 10)) =
        afterEmit graph n placement output vertex ports direction base (placement (.inl 10)) :=
      PoweringMachineRowHeaders.finalTapes_other _ _ _ _ _ _ _ _ _
        (hother _) (hother _) (hother _) (hother _) (fun i => hother _)
    _ = [] := afterEmit_data graph n placement output outside vertex ports direction base

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    Ready graph n placement vertex suffix (finalTapes graph n placement output vertex ports direction base) := by
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hrole (j : Fin 11) (h₂ : j ≠ 2) (h₃ : j ≠ 3) (h₄ : j ≠ 4) (h₁₀ : j ≠ 10) :
      finalTapes graph n placement output vertex ports direction base (placement (.inl j)) =
        afterEmit graph n placement output vertex ports direction base (placement (.inl j)) := by
    have h := PoweringMachineRowHeaders.finalTapes_shared graph n (by unfold capacity; omega)
      (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
      vertex ports direction (afterEmit graph n placement output vertex ports direction base) j h₂ h₃ h₄ h₁₀
    dsimp only [finalTapes]
    simpa only [headerPlacement, ite_eq_right (show (Sum.inl j : PoweringMachineTapes.Tape (capacity n)) ≠ .inl 10 from
      fun heq => h₁₀ (Sum.inl.inj heq))] using h
  constructor
  · constructor
    · rw [hrole 0 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.table
    · rw [hrole 1 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.source
    · rw [hrole 5 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.scratch
    · rw [hrole 8 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.leftCopy
    · rw [hrole 9 (by decide) (by decide) (by decide) (by decide)]; exact hm.1.rightCopy
  · exact finalTapes_data graph n placement distinct output outside vertex ports direction base

def budget (d n inputLength : Nat) : Nat :=
  PoweringPlanBudget.rowBudget d n inputLength + 1 +
    ((14 * (n + 1) + 4) * inputLength + 12 * (n + 1) + 6)

end MinUncutGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineVertex
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringMachineVertex

open _root_.Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

def result (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (j : Command d n) (base : K → List Bool) :
    K → List Bool :=
  PoweringMachineRowBody.finalTapes graph n placement output vertex (ports j) (direction j) base

def sequenceTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) :
    K → List Bool :=
  MachineFiniteSequence.resultOf (result graph n placement output vertex) ops base

def finalTapes (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (vertex : Fin vertices) (base : K → List Bool) : K → List Bool :=
  sequenceTapes graph n placement output vertex (commands d n) base

def budget (d n inputLength : Nat) : Nat :=
  PoweringTableLayout.blockSize d n * PoweringMachineRowBody.budget d n inputLength

theorem sequenceTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (sequenceTapes graph n placement output vertex ops base) := by
  induction ops generalizing base with
  | nil => exact ready
  | cons j ops ih =>
      apply ih
      exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
        vertex (ports j) (direction j) base suffix ready

theorem finalTapes_ready (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    PoweringMachineRowBody.Ready graph n placement vertex suffix
      (finalTapes graph n placement output vertex base) :=
  sequenceTapes_ready graph n placement distinct output outside vertex (commands d n) base suffix ready

end MinUncutGames.Foundations.Complexity.PoweringMachineVertex

namespace MinUncutGames.Foundations.Complexity.PoweringMachineOuterLoop

open _root_.Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

abbrev Placement (K : Type) (n : Nat) := PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K

structure Ready (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (base : K → List Bool) : Prop where
  table : base (placement (.inl 0)) = PortTables.tableBits graph
  scratch : base (placement (.inl 5)) = []
  leftCopy : base (placement (.inl 8)) = []
  rightCopy : base (placement (.inl 9)) = []
  data : base (placement (.inl 10)) = []

def counter (placement : Placement K n) (base : K → List Bool) (remaining : Nat) : K → List Bool :=
  MachineUnaryCounter.counterTapes (placement (.inl 1)) base remaining []

theorem counter_other (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (remaining : Nat) (j : Fin 11) (hj : j ≠ 1) :
    counter placement base remaining (placement (.inl j)) = base (placement (.inl j)) := by
  apply MachineUnaryCounter.counterTapes_other
  intro h
  exact hj (Sum.inl.inj (distinct h))

theorem ready_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (base : K → List Bool) (ready : Ready graph n placement base) (vertex : Fin vertices) :
    PoweringMachineRowBody.Ready graph n placement vertex [] (counter placement base vertex.val) := by
  constructor
  · constructor
    · rw [counter_other placement distinct base vertex.val 0 (by decide)]
      exact ready.table
    · simp only [counter, MachineUnaryCounter.counterTapes_counter]
    · rw [counter_other placement distinct base vertex.val 5 (by decide)]
      exact ready.scratch
    · rw [counter_other placement distinct base vertex.val 8 (by decide)]
      exact ready.leftCopy
    · rw [counter_other placement distinct base vertex.val 9 (by decide)]
      exact ready.rightCopy
  · rw [counter_other placement distinct base vertex.val 10 (by decide)]
    exact ready.data

omit [DecidableEq K] in
theorem ready_of_vertex (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (base : K → List Bool) (vertex : Fin vertices)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex [] base) :
    Ready graph n placement base :=
  ⟨ready.1.table, ready.1.scratch, ready.1.leftCopy, ready.1.rightCopy, ready.2⟩

theorem vertexEntry (d n : Nat) (labels : PoweringMachineVertex.Label d n → Λ) (guardLabel : Λ) :
    PoweringMachineVertex.entry d n labels (some guardLabel) =
      some (vertexStart d n labels guardLabel) := by
  unfold vertexStart PoweringMachineVertex.entry PoweringMachineVertex.sequenceEntry
  have h : ∀ (commands : List (PoweringMachineVertex.Command d n))
      (labels : MachineFiniteSequence.Label PoweringMachineVertex.LocalLabel commands → Λ),
      MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel) =
      some ((MachineFiniteSequence.entry PoweringMachineVertex.LocalLabel
        (fun j => PoweringMachineRowBody.entry n
          (PoweringMachineVertex.ports j) (PoweringMachineVertex.direction j))
        commands labels (some guardLabel)).getD guardLabel) := by
    intro commands labels
    cases commands <;> rfl
  exact h _ labels

def finalTapes (graph : PortTables.Table vertices d) (n : Nat) (placement : Placement K n)
    (output : K) : (remaining : Nat) → remaining ≤ vertices → (K → List Bool) → K → List Bool
  | 0, _, base => counter placement base 0
  | r + 1, bounded, base =>
      finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output ⟨r, by omega⟩
          (counter placement base r))

end MinUncutGames.Foundations.Complexity.PoweringMachineOuterLoop

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineGlobal
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineGlobal

open _root_.Turing

def inputTape (n : Nat) : Tape n :=
  placement n (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))

instance labelFintype (d n : Nat) : Fintype (Label d n) :=
  inferInstanceAs (Fintype (PoweringMachineInitialize.Label ⊕
    (Bool ⊕ (PoweringMachineVertex.Label d n ⊕ FinishLabel n))))

def main (d n : Nat) : Label d n := initLabels d n (.inr .seed)

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

end MinUncutGames.Foundations.Complexity.PoweringMachineGlobal

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_PoweringInitializeFrame
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.PoweringInitializeFrame

open _root_.Turing PCP

variable {vertices d : Nat}

theorem prepared_commonRole (graph : PortTables.Table vertices d) (n : Nat)
    (j : Fin 11) (hne : j ≠ 1) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl j)) =
      if j = 0 then PortTables.tableBits graph else [] := by
  simp [preparedTapes, PoweringMachineGlobal.placement,
    PoweringMachineInitialize.commonPlacement, PoweringMachineTapes.start,
    PoweringMachineInitialize.mergeTapes, initialExtra, PoweringMachineTapes.table, hne]

theorem prepared_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) := by
  constructor
  · simpa using prepared_commonRole graph n 0 (by decide)
  · simpa using prepared_commonRole graph n 5 (by decide)
  · simpa using prepared_commonRole graph n 8 (by decide)
  · simpa using prepared_commonRole graph n 9 (by decide)
  · simpa using prepared_commonRole graph n 10 (by decide)

theorem prepared_counter (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.counter (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) vertices = preparedTapes graph n := by
  unfold PoweringMachineOuterLoop.counter MachineUnaryCounter.counterTapes
  rw [List.append_nil, ← prepared_start graph n]
  simp only [Function.update_eq_self]

@[simp] theorem prepared_source (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (.inl PoweringMachineLoop.HeaderTape.source) = [] := rfl

def preparedCfg (graph : PortTables.Table vertices d) (n : Nat) :
    (PoweringMachineGlobal.machine d n).Cfg :=
  ⟨some (PoweringMachineGlobal.guardLabel d n),
    PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), preparedTapes graph n⟩

theorem initialGlobalTapes_eq (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n) =
      fun tape => if tape = PoweringMachineGlobal.inputTape n
        then PortTables.tableBits graph else [] := by
  funext tape
  cases tape with
  | inl field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table]
  | inr field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table, initialExtra]

theorem machine_initialStacks (d n : Nat) (input : List Bool) :
    (initList (PoweringMachineGlobal.machine d n) input).stk =
      fun tape => if tape = PoweringMachineGlobal.inputTape n then input else [] := by
  funext tape
  rfl

theorem initList_eq (graph : PortTables.Table vertices d) (n : Nat) :
    initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph) =
      ⟨some (PoweringMachineGlobal.main d n),
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n)⟩ := by
  have ht := (machine_initialStacks d n (PortTables.tableBits graph)).trans
    (initialGlobalTapes_eq graph n).symm
  exact congrArg (TM2.Cfg.mk _ _) ht

theorem tableBits_head (graph : PortTables.Table vertices d) :
    PortTables.tableBits graph = encodeWord vertices ++
      encodeWords (PortTables.tableWords graph).tail := rfl

end MinUncutGames.Foundations.Complexity.PoweringInitializeFrame

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_PoweringPolynomialBudget
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringPolynomialBudget

open PCP

noncomputable def rowTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringMachineRowBody.bufferSize d n) *
      (Polynomial.C (28 * (2 * (n + 1)) + 10) * Polynomial.X +
        Polynomial.C (24 * (2 * (n + 1)) + 15)) + Polynomial.C 1 +
    (Polynomial.C (14 * (n + 1) + 4) * Polynomial.X +
      Polynomial.C (12 * (n + 1)) + Polynomial.C 6)

@[simp] theorem rowTime_eval (d n inputLength : Nat) :
    (rowTime d n).eval inputLength = PoweringMachineRowBody.budget d n inputLength := by
  simp only [rowTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, PoweringMachineRowBody.budget, PoweringPlanBudget.rowBudget,
    PoweringPlanBudget.fieldBudget, PoweringMachineRowBody.bufferSize, Nat.add_assoc]

noncomputable def vertexTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringTableLayout.blockSize d n) * rowTime d n

@[simp] theorem vertexTime_eval (d n inputLength : Nat) :
    (vertexTime d n).eval inputLength = PoweringMachineVertex.budget d n inputLength := by
  simp only [vertexTime, Polynomial.eval_mul, Polynomial.eval_C, rowTime_eval,
    PoweringMachineVertex.budget]

end MinUncutGames.Foundations.Complexity.PoweringPolynomialBudget

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudPrefix
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineCloudPrefix

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP
open scoped BigOperators

variable {σ : Type}

def inputLength (t : GraphTables.Table) (b : Nat) (suffix : List Bool) : Nat :=
  (GraphTables.tableBits t).length + (encodeWord b ++ suffix).length

end MinUncutGames.Foundations.Complexity.MachineCloudPrefix

namespace MinUncutGames.Foundations.Complexity.MachinePreservingLookupClean

open _root_.Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem remaining_length_le (values : List Nat) (index : Nat) :
    (encodeWords (values.drop (index + 1))).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop (index + 1) values)
  simp only [encodeWords_append, List.length_append] at h
  omega

theorem initialTapes_eq (tape : Fin 5 → K) (base : K → List Bool)
    (index : Nat) (indexSuffix : List Bool)
    (counterWord : base (tape 1) = encodeWord index ++ indexSuffix)
    (workEmpty : base (tape 2) = []) :
    MachinePreservingLookup.initialTapes tape base index indexSuffix [] (base (tape 3)) =
      base := by
  simp only [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
    ← counterWord, ← workEmpty, Function.update_eq_self]

end MinUncutGames.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularLift
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudRank

open _root_.Turing MachineComposition MachineCloudCount

variable {σ : Type}

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 3 * (encodeWords (rs.flatMap rowWords)).length + 2 := by
  induction rs with
  | nil => simp only [prefixTime, List.flatMap_nil, encodeWords, List.length_nil,
      Nat.mul_zero, Nat.zero_add, le_refl]
  | cons r rs ih =>
      have hr := rowTime_le v r
      simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
      omega

theorem encoded_rows_split (rs : List Row) (k : Nat) :
    encodeWords (rs.flatMap rowWords) =
      encodeWords ((rs.take k).flatMap rowWords) ++
        encodeWords ((rs.drop k).flatMap rowWords) := by
  have h := congrArg (fun xs : List Row => encodeWords (xs.flatMap rowWords))
    (List.take_append_drop k rs)
  simpa only [List.flatMap_append, encodeWords_append] using h.symm

open MinUncutGames.Foundations.PCP

theorem tableRows_length (t : GraphTables.Table) : (tableRows t).length = t.darts := by
  simp only [tableRows, List.length_map, GraphTables.rowList_length]

theorem cloudRank_eq_prefix_count (t : GraphTables.Table) (v : Fin t.vertices)
    (e : DegreeReplacement.Cloud (GraphTables.semantics t) v) :
    (PreprocessingCloudIndex.cloudRank t v e).val =
      rowsHits v.val ((tableRows t).take e.val.val) := by
  have hindex := idxOf_filter_prefix (fun x : Fin t.darts => decide (t.rows[x].tail = v))
    e.val (by simpa using e.property) (List.finRange t.darts) (List.mem_finRange e.val)
  simp only [List.idxOf_finRange] at hindex
  change (PreprocessingCloudIndex.cloudDarts t v).idxOf e.val = _
  unfold PreprocessingCloudIndex.cloudDarts
  rw [hindex, rowsHits_eq_filter]
  simp only [tableRows, rowList_eq_finRange_map, ← List.map_take, List.filter_map,
    List.length_map, Function.comp_def, Fin.val_inj]

end MinUncutGames.Foundations.Complexity.MachineCloudRank

end
section
namespace MinUncutGames.Foundations.Complexity.MachineTableRows

open _root_.Turing
open PCP.GraphTables

variable {K Λ σ : Type} [DecidableEq K]

theorem rowBits_eq {n m : Nat} (r : DartRow n m) :
    encodeWords (rowWords r) = encodeWord r.tail.val ++
      encodeWord r.reverseIndex.val ++ encodeWords (relationWords r.relation) := by
  simp [rowWords, encodeWords]

end MinUncutGames.Foundations.Complexity.MachineTableRows

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalRow

open _root_.Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingRegularTables

def prefixWords (t : Table) (e : Fin t.darts) : List Nat :=
  [t.vertices, t.darts] ++ ((rowList t).take e.val).flatMap rowWords

def suffixWords (t : Table) (e : Fin t.darts) : List Nat :=
  ((rowList t).drop (e.val + 1)).flatMap rowWords

theorem prefixWords_length (t : Table) (e : Fin t.darts) :
    (prefixWords t e).length = 2 + 4098 * e.val := by
  simp only [prefixWords, List.length_append, List.length_cons, List.length_nil,
    rowsWords_length, List.length_take, rowList_length, Nat.min_eq_left e.isLt.le]

theorem tableWords_at_row (t : Table) (e : Fin t.darts) :
    GraphTables.tableWords t = prefixWords t e ++ (rowWords t.rows[e] ++ suffixWords t e) := by
  have he : e.val < (rowList t).length := by simpa only [rowList_length] using e.isLt
  have hs : (rowList t).take e.val ++ (rowList t)[e.val] ::
      (rowList t).drop (e.val + 1) = rowList t := by
    rw [List.getElem_cons_drop he, List.take_append_drop]
  have hw := congrArg (fun rs : List (DartRow t.vertices t.darts) => rs.flatMap rowWords) hs
  simp only [List.flatMap_append, List.flatMap_cons, rowList, Vector.getElem_toList] at hw
  unfold GraphTables.tableWords prefixWords suffixWords rowList
  rw [← hw]
  simp only [List.append_assoc, Fin.getElem_fin]

theorem tableWords_drop_row (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t).drop (2 + 4098 * e.val) = rowWords t.rows[e] ++ suffixWords t e := by
  rw [tableWords_at_row]
  exact List.drop_left' (l₂ := rowWords t.rows[e] ++ suffixWords t e)
    (prefixWords_length t e)

theorem selected_reverse (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t)[4098 * e.val + 3]? = some t.rows[e].reverseIndex.val := by
  have h := congrArg (fun words : List Nat => words[1]?) (tableWords_drop_row t e)
  simp only [List.getElem?_drop] at h
  rw [show 2 + 4098 * e.val + 1 = 4098 * e.val + 3 by omega] at h
  simpa [rowWords] using h

theorem remaining_relation (t : Table) (e : Fin t.darts) :
    (GraphTables.tableWords t).drop (4098 * e.val + 3 + 1) =
      relationWords t.rows[e].relation ++ suffixWords t e := by
  rw [show 4098 * e.val + 3 + 1 = (2 + 4098 * e.val) + 2 by omega,
    ← List.drop_drop, tableWords_drop_row]
  simp only [rowWords, List.cons_append, List.drop_succ_cons, List.drop_zero, List.nil_append]

def looked (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Tape → List Bool :=
  MachineAffineLookup.finalTapes lookupTape base (GraphTables.tableWords t) (4098 * e.val + 3)
    t.rows[e].reverseIndex.val

def copied (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (looked t e base) 3
    (encodeWords (suffixWords t e) ++ base 3)) 7
    (encodeWords (relationWords t.rows[e].relation) ++ base 7)

def affined (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (copied t e base) 6
    (encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) ++ base 6)

theorem looked_other (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) :
    looked t e base k = base k :=
  MachineAffineLookup.finalTapes_other lookupTape base _ _ _ k h₂ h₃ h₄

theorem looked_reverse (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ base 4 :=
  MachineAffineLookup.finalTapes_output lookupTape base _ _ _

theorem looked_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    looked t e base 3 = encodeWords (relationWords t.rows[e].relation) ++
      (encodeWords (suffixWords t e) ++ base 3) := by
  change MachineLookup.tapes (2 : Tape) 3 4 base
    (encodeWord 0 ++ base 2)
    (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
    (encodeWord t.rows[e].reverseIndex.val ++ base 4) 3 = _
  rw [MachineLookup.tapes_source _ _ _ (by decide), remaining_relation, encodeWords_append]
  exact List.append_assoc _ _ _

theorem vectorBits_eq_encodedBlock {n : Nat} (relation : Vector Bool n) :
    PoweringMachineRow.encodeBits (List.ofFn (fun i : Fin n => relation[i])) =
      encodeWords (relation.toList.map GraphTables.bitWord) := by
  rw [PoweringMachineRow.encodeBits_graphWords]
  congr 1
  congr 1
  have hvec : Vector.ofFn (fun i : Fin n => relation[i]) = relation := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, Fin.getElem_fin]
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList hvec)

theorem relationBits_eq_encodedBlock (relation : RelationTable) :
    PoweringMachineRow.encodeBits (List.ofFn (fun i : Fin 4096 => relation[i])) =
      encodeWords (relationWords relation) := vectorBits_eq_encodedBlock relation

theorem copied_other (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₇ : k ≠ 7) :
    copied t e base k = base k := by
  simp only [copied, Function.update_of_ne h₇, Function.update_of_ne h₃,
    looked_other t e base k h₂ h₃ h₄]

theorem copied_reverse (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    copied t e base 4 = encodeWord t.rows[e].reverseIndex.val ++ base 4 := by
  simp only [copied, Function.update_of_ne (by decide : (4 : Tape) ≠ 7),
    Function.update_of_ne (by decide : (4 : Tape) ≠ 3), looked_reverse]

theorem copied_relation (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    copied t e base 7 = encodeWords (relationWords t.rows[e].relation) ++ base 7 := by
  simp only [copied, Function.update_self]

theorem affined_other (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool)
    (k : Tape) (h₂ : k ≠ 2) (h₃ : k ≠ 3) (h₄ : k ≠ 4) (h₆ : k ≠ 6) (h₇ : k ≠ 7) :
    affined q t e base k = base k := by
  simp only [affined, Function.update_of_ne h₆, copied_other t e base k h₂ h₃ h₄ h₇]

theorem affined_reverse (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    affined q t e base 6 = encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) ++ base 6 := by
  simp only [affined, Function.update_self]

theorem affined_relation (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    affined q t e base 7 = encodeWords (relationWords t.rows[e].relation) ++ base 7 := by
  simp only [affined, Function.update_of_ne (by decide : (7 : Tape) ≠ 6), copied_relation]

structure Input (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Prop where
  indexWord : base 0 = encodeWord e.val
  tableWord : base 1 = tableBits t
  reverseEmpty : base 4 = []
  scratchEmpty : base 5 = []
  computedEmpty : base 6 = []
  relationEmpty : base 7 = []
  rowEmpty : base 8 = []

def emittedWords (q : Nat) (t : Table) (e : Fin t.darts) : List Nat :=
  e.val :: ((q + 1) * t.rows[e].reverseIndex.val + q) :: relationWords t.rows[e].relation

theorem affined_fields (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    MachineTableRows.fieldBits fields (affined q t e base) = encodeWords (emittedWords q t e) := by
  have htail := affined_other q t e base 0 (by decide) (by decide) (by decide)
    (by decide) (by decide)
  simp only [MachineTableRows.fieldBits, fields_zero, fields_one, fields_two,
    htail, input.indexWord, affined_reverse, input.computedEmpty,
    affined_relation, input.relationEmpty, List.append_nil,
    emittedWords, encodeWords, List.append_assoc]

def rowSteps (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Nat :=
  4 * (encodeWords (emittedWords q t e)).length + 2 * (base 9).length + 9

def finalTapes (q : Nat) (t : Table) (e : Fin t.darts) (base : Tape → List Bool) :
    Tape → List Bool :=
  Function.update (affined q t e base) 9 (base 9 ++ encodeWords (emittedWords q t e))

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalRow

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCloudSelect
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineCloudSelect

open _root_.Turing MachineComposition
open MachineCloudCount (Row rowWords rowTime rowsHits tableRows)

variable {σ : Type}

theorem compareTrace (original suffix targetSuffix rank position : List Bool)
    (x v : Nat) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[x + min x v + 3]
      (some (cfg (some (.inl .field)) .checking original (encodeWord x ++ suffix)
        (encodeWord v ++ targetSuffix) [] rank position ambient register)) =
      some (cfg (some (.inr .dispatch)) .checking original suffix
        (encodeWord v ++ targetSuffix) (List.replicate (if x = v then 1 else 0) true)
        rank position ambient none) := by
  have h := MachineCloudCount.preservingFieldTrace BaseLabel.field BaseLabel.restore BaseLabel.done
    baseProgram rfl rfl original suffix targetSuffix [] rank x v ambient register
  simp only [List.append_nil] at h
  have hhalt : (advance (TM2.step baseProgram))^[x + min x v + 3]
      (some ⟨some .field, ((ambient, false), register),
        MachineCloudCount.memory original (encodeWord x ++ suffix)
          (encodeWord v ++ targetSuffix) [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix (encodeWord v ++ targetSuffix) []
          (List.replicate (if x = v then 1 else 0) true) rank⟩ := by
    rw [show x + min x v + 3 = (x + min x v + 2) + 1 by omega,
      Function.iterate_succ_apply', h, advance_some]
    rfl
  convert liftTrace Phase.checking position _ _ _ hhalt using 1 <;> rfl

theorem dispatch_hit_succ (original work target rankSuffix position : List Bool)
    (rank : Nat) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [true] (encodeWord (rank + 1) ++ rankSuffix) position ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original work target []
        (encodeWord rank ++ rankSuffix) position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord, List.replicate_succ]

theorem dispatch_hit_zero (original work target rankSuffix position : List Bool) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .checking
      original work target [true] (encodeWord 0 ++ rankSuffix) position ambient none) =
      some (cfg (some (.inl .clearWork)) .finishing
        original work target [] rankSuffix position ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord]

theorem advanceStep (original work target rank positionSuffix : List Bool)
    (position : Nat) (ambient : σ) :
    TM2.step program (cfg (some (.inr .dispatch)) .advancing original work target []
      rank (encodeWord position ++ positionSuffix) ambient none) =
      some (cfg (some (.inl .field)) .checking original work target []
        rank (encodeWord (position + 1) ++ positionSuffix) ambient none) := by
  simp [program, MachineEmbedding.program, extra, dispatcher, go, TM2.stepAux, TM2.step,
    cfg, encodeWord, List.replicate_succ]

theorem initializeStep (original target output : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program (cfg (some (.inr .initialize_)) .checking
      original [] target [] [] output ambient register) =
      some (cfg (some (.inl .queryFirst)) .checking
        original [] target [] [] (encodeWord 0 ++ output) ambient none) := by
  simp [program, MachineEmbedding.program, extra, go, TM2.stepAux, TM2.step, cfg, encodeWord]

theorem skipTrace (fields : List Nat) (hwidth : fields.length = 4097)
    (original suffix target rank position : List Bool) (ambient : σ) :
    (advance (TM2.step program))^[(encodeWords fields).length + 1]
      (some (cfg (some (.inl (skipLabel 0))) .advancing original
        (encodeWords fields ++ suffix) target [] rank position ambient none)) =
      some (cfg (some (.inr .dispatch)) .advancing
        original suffix target [] rank position ambient none) := by
  have h := MachineCloudCount.discardFieldsTrace skipLabel (baseProgram (σ := σ)) fields 0
    (by intro i hi; simpa only [Nat.zero_add] using baseProgram_skip (hwidth ▸ hi))
    original suffix target [] [] rank ambient false none
  have hnonempty : fields ≠ [] := by intro h; simp [h] at hwidth
  simp only [Nat.zero_add, hwidth, skipLabel, lt_self_iff_false, ↓reduceDIte,
    hnonempty, ite_false] at h
  have raw : (advance (TM2.step baseProgram))^[(encodeWords fields).length + 1]
      (some ⟨some (skipLabel 0), ((ambient, false), none),
        MachineCloudCount.memory original (encodeWords fields ++ suffix) target [] [] rank⟩) =
      some ⟨none, ((ambient, false), none),
        MachineCloudCount.memory original suffix target [] [] rank⟩ := by
    rw [Function.iterate_succ_apply']
    simp only [skipLabel, dite_eq_left (by decide : 0 < 4097)] at h ⊢
    rw [h, advance_some]
    rfl
  convert liftTrace Phase.advancing position _ _ _ raw using 1 <;> rfl

theorem rowSkipTrace (r : Row) (hwidth : r.2.length = 4097) (v rank position : Nat)
    (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[rowTime v r + 3]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rowWords r) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + 1) ++ outputSuffix) ambient none) := by
  have hcompare := compareTrace original (encodeWords r.2 ++ suffix) targetSuffix
    (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
    (encodeWord position ++ outputSuffix) r.1 v ambient register
  have hdispatch : TM2.step program
      (cfg (some (.inr .dispatch)) .checking original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) (List.replicate (if r.1 = v then 1 else 0) true)
        (encodeWord (rank + if r.1 = v then 1 else 0) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) =
      some (cfg (some (.inl (skipLabel 0))) .advancing original (encodeWords r.2 ++ suffix)
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient none) := by
    by_cases hit : r.1 = v
    · simpa only [ite_eq_left hit, List.replicate_succ, List.replicate_zero] using
        dispatch_hit_succ original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          rankSuffix (encodeWord position ++ outputSuffix) rank ambient
    · simpa only [ite_eq_right hit, Nat.add_zero, List.replicate_zero] using
        dispatch_miss original (encodeWords r.2 ++ suffix) (encodeWord v ++ targetSuffix)
          (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have hskip := skipTrace r.2 hwidth original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) (encodeWord position ++ outputSuffix) ambient
  have ht : rowTime v r + 3 =
      1 + (((encodeWords r.2).length + 1) + (1 + (r.1 + min r.1 v + 3))) := by
    simp only [rowTime, rowWords, encodeWords, List.length_append, encodeWord_length]
    omega
  rw [ht, Function.iterate_add_apply _ 1,
    Function.iterate_add_apply _ ((encodeWords r.2).length + 1),
    Function.iterate_add_apply _ 1]
  simp only [rowWords, encodeWords, List.append_assoc]
  rw [hcompare, Function.iterate_one, advance_some, hdispatch, hskip,
    advance_some]
  exact advanceStep original suffix (encodeWord v ++ targetSuffix)
    (encodeWord rank ++ rankSuffix) outputSuffix position ambient

theorem prefixTrace (rs : List Row) (hwidth : ∀ r ∈ rs, r.2.length = 4097)
    (v rank position : Nat) (original suffix targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v rs]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (rs.flatMap rowWords) ++ suffix) (encodeWord v ++ targetSuffix) []
        (encodeWord (rowsHits v rs + rank) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg (some (.inl .field)) .checking original suffix
        (encodeWord v ++ targetSuffix) [] (encodeWord rank ++ rankSuffix)
        (encodeWord (position + rs.length) ++ outputSuffix) ambient
        (if rs = [] then register else none)) := by
  induction rs generalizing position register with
  | nil => simp [prefixTime, rowsHits, encodeWords]
  | cons r rs ih =>
    have hrow := rowSkipTrace r (hwidth r (by simp)) v (rowsHits v rs + rank) position
      original (encodeWords (rs.flatMap rowWords) ++ suffix) targetSuffix rankSuffix
      outputSuffix ambient register
    have hrest := ih (by intro x hx; exact hwidth x (by simp [hx])) (position + 1) none
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.append_assoc]
    rw [Function.iterate_add_apply]
    have hi : (if r.1 = v then 1 else 0) + rowsHits v rs + rank =
        (rowsHits v rs + rank) + (if r.1 = v then 1 else 0) := by omega
    simp only [rowsHits, hi]
    rw [hrow]
    simpa only [ite_self, List.cons_ne_nil, ite_false, List.length_cons,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

theorem selectedTrace (v : Nat) (original work targetSuffix rankSuffix position : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original (encodeWord v ++ work)
        (encodeWord v ++ targetSuffix) [] (encodeWord 0 ++ rankSuffix) position ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] [] position ambient none) := by
  have hcompare := compareTrace original work targetSuffix (encodeWord 0 ++ rankSuffix)
    position v v ambient register
  simp only [ite_true, List.replicate_succ, List.replicate_zero] at hcompare
  rw [show 2 * v + work.length + rankSuffix.length + 8 =
      (work.length + rankSuffix.length + 4) + (1 + (v + min v v + 3)) by
        simp only [Nat.min_self]; omega,
    Function.iterate_add_apply _ (work.length + rankSuffix.length + 4),
    Function.iterate_add_apply _ 1, hcompare, Function.iterate_one, advance_some,
    dispatch_hit_zero]
  exact cleanupTrace original work (encodeWord v ++ targetSuffix) rankSuffix position ambient

theorem prefixSelectedTrace (preceding : List Row)
    (hwidth : ∀ r ∈ preceding, r.2.length = 4097) (v position : Nat)
    (original work targetSuffix rankSuffix outputSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8]
      (some (cfg (some (.inl .field)) .checking original
        (encodeWords (preceding.flatMap rowWords) ++ (encodeWord v ++ work))
        (encodeWord v ++ targetSuffix) [] (encodeWord (rowsHits v preceding) ++ rankSuffix)
        (encodeWord position ++ outputSuffix) ambient register)) =
      some (cfg none .checking original [] (encodeWord v ++ targetSuffix) [] []
        (encodeWord (position + preceding.length) ++ outputSuffix) ambient none) := by
  have hp := prefixTrace preceding hwidth v 0 position original (encodeWord v ++ work)
    targetSuffix rankSuffix outputSuffix ambient register
  simp only [Nat.add_zero] at hp
  have hs := selectedTrace v original work targetSuffix rankSuffix
    (encodeWord (position + preceding.length) ++ outputSuffix) ambient
    (if preceding = [] then register else none)
  rw [show prefixTime v preceding + 2 * v + work.length + rankSuffix.length + 8 =
      (2 * v + work.length + rankSuffix.length + 8) + prefixTime v preceding by omega,
    Function.iterate_add_apply, hp]
  exact hs

theorem prefixTime_le (v : Nat) (rs : List Row) :
    prefixTime v rs ≤ 6 * (encodeWords (rs.flatMap rowWords)).length := by
  induction rs with
  | nil => simp [prefixTime, encodeWords]
  | cons r rs ih =>
    have hr := MachineCloudCount.rowTime_le v r
    have hpos : 1 ≤ (encodeWords (rowWords r)).length := by
      simp only [rowWords, encodeWords, List.length_append, encodeWord_length]
      omega
    simp only [prefixTime, List.flatMap_cons, encodeWords_append, List.length_append]
    omega

open MinUncutGames.Foundations.PCP

def remainder (t : GraphTables.Table) (e : Fin t.darts) : List Bool :=
  encodeWords (t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) ++
    encodeWords (((tableRows t).drop (e.val + 1)).flatMap rowWords)

theorem tableRows_getElem (t : GraphTables.Table) (e : Fin t.darts) :
    (tableRows t)[e.val]'(by rw [MachineCloudRank.tableRows_length]; exact e.isLt) =
      (t.rows[e].tail.val, t.rows[e].reverseIndex.val :: GraphTables.relationWords t.rows[e].relation) := by
  simp only [MachineCloudCount.tableRows, MachineCloudCount.rowList_eq_finRange_map,
    List.getElem_map, List.getElem_finRange]
  apply congrArg (fun j : Fin t.darts =>
    (t.rows[j].tail.val, t.rows[j].reverseIndex.val :: GraphTables.relationWords t.rows[j].relation))
  apply Fin.ext
  rfl

theorem tableWord_split (t : GraphTables.Table) (v : Fin t.vertices) (e : Fin t.darts)
    (owner : t.rows[e].tail = v) :
    encodeWords ((tableRows t).flatMap rowWords) =
      encodeWords (((tableRows t).take e.val).flatMap rowWords) ++
        (encodeWord v.val ++ remainder t e) := by
  have he : e.val < (tableRows t).length := by
    rw [MachineCloudRank.tableRows_length]
    exact e.isLt
  rw [MachineCloudRank.encoded_rows_split (tableRows t) e.val, List.drop_eq_getElem_cons he]
  simp only [List.flatMap_cons, encodeWords_append]
  rw [tableRows_getElem]
  simp only [rowWords, encodeWords, owner, remainder, List.append_assoc]

end MinUncutGames.Foundations.Complexity.MachineCloudSelect

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderRowControl
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

theorem firstAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    firstAddress vertex.val s =
      (rowIndex v (degree d) (vertex,firstOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

theorem secondAddress_eq_rowIndex {v d : Nat} (vertex : Fin v) (s : Control d) :
    secondAddress vertex.val s =
      (rowIndex v (degree d) (vertex,secondOffset s)).val := by
  rw [rowIndex_val]
  exact Nat.add_comm _ _

end MinUncutGames.Foundations.PCP.ExpanderRowControl

end
section
namespace MinUncutGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open MinUncutGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

theorem rotationWords_getElem? (table : Table v d) (i : Fin (v * d)) :
    (rotationWords table)[i.val]? = some (reverseIndex table i).val := by
  apply List.getElem?_eq_some_iff.mpr
  exact ⟨by simpa only [rotationWords_length] using i.isLt,
    rotationWords_getElem table i.val i.isLt⟩

theorem rotationWords_entry_lt (table : Table v d) (n : ℕ)
    (hn : n ∈ rotationWords table) : n < v * d := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hn
  exact a.isLt

theorem rotationWords_lookup (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[(rowIndex v d x).val]? =
      some (rowIndex v d (lookup table x)).val := by
  simpa only [lookup, Equiv.apply_symm_apply] using
    rotationWords_getElem? table (rowIndex v d x)

theorem rotationWords_row_order (table : Table v d) (x : Fin v × Fin d) :
    (rotationWords table)[x.2.val + d * x.1.val]? =
      some ((lookup table x).2.val + d * (lookup table x).1.val) := by
  simpa only [rowIndex_val] using rotationWords_lookup table x

theorem encode_rotationWords_length_le (table : Table v d) :
    (encodeWords (rotationWords table)).length ≤ (v * d) * (v * d + 1) := by
  calc
    _ ≤ (rotationWords table).length * (v * d + 1) :=
      Complexity.encodeWords_length_le _ _
        (fun n hn => (rotationWords_entry_lt table n hn).le)
    _ = _ := by rw [rotationWords_length]

end MinUncutGames.Foundations.PCP.ExpanderTableWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFixedDivMod
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineFixedDivMod

open _root_.Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord )

variable {K Λ σ : Type} [DecidableEq K]

theorem scanStep_succ (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
      unaryTapes source quotient remainder base (n + 1) (k / d) 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨some scanLabel, ((ambient, residue d positive (k + 1)), some true),
        unaryTapes source quotient remainder base n ((k + 1) / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, residue d positive k), register)
    (unaryTapes source quotient remainder base (n + 1) (k / d) 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atScan]
  simp only [unaryTapes, encodeWord, List.replicate_succ, List.cons_append]
  rw [scanAux_true d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder, nextResidue_residue]
  by_cases hmod : (k + 1) % d = 0
  · rw [Nat.succ_div_of_mod_eq_zero hmod]
    simp [residue, hmod, List.replicate_succ]
  · rw [Nat.succ_div_of_mod_ne_zero hmod]
    simp [residue, hmod]

theorem scanStep_zero (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, r), register),
      unaryTapes source quotient remainder base 0 q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨some (emitterLabel r), ((ambient, r), some false),
        unaryTapes source quotient remainder base 0 q 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program scanLabel) ((ambient, r), register)
    (unaryTapes source quotient remainder base 0 q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atScan]
  simp only [unaryTapes, encodeWord, List.replicate_zero, List.nil_append,
    List.singleton_append]
  rw [scanAux_false d positive source quotient remainder sourceQuotient sourceRemainder
    quotientRemainder]

theorem emitterStep (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (emitterLabel : Fin d → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some (emitterLabel r), ((ambient, r), register),
      unaryTapes source quotient remainder base n q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base n q r.val
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program (emitterLabel r)) ((ambient, r), register)
    (unaryTapes source quotient remainder base n q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atEmitter]
  unfold emitter
  rw [stepAux_pushWord]
  simp only [unaryTapes, MachineCopy.forkTapes_right, List.reverse_replicate]
  rw [update_remainder]
  cases exit <;>
    simp [TM2.stepAux, Reduction.MachineTransfer.exitAt, encodeWord, List.append_assoc]

theorem trace_fromCount (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base n (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 ((k + n) / d) ((k + n) % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  induction n generalizing k register with
  | zero =>
    change (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
      unaryTapes source quotient remainder base 0 (k / d) 0
        sourceSuffix quotientSuffix remainderSuffix⟩).bind (TM2.step program) = _
    rw [scanStep_zero d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan, Option.bind_some]
    simpa only [residue, Nat.add_zero] using
      emitterStep d positive source quotient remainder emitterLabel exit program atEmitter
        base 0 (k / d) sourceSuffix quotientSuffix remainderSuffix ambient
        (residue d positive k) (some false)
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 2]
      (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base (n + 1) (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) = _
    rw [scanStep_succ d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) (some true)

theorem divModTrace (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) = emitter d positive remainder exit r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register),
        unaryTapes source quotient remainder base n 0 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((ambient, residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  simpa only [Nat.zero_add, Nat.zero_div] using
    trace_fromCount d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel exit program atScan atEmitter base n 0
      sourceSuffix quotientSuffix remainderSuffix ambient register

theorem scanTrace_fromCount (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (base : K → List Bool) (n k : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base n (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨some (emitterLabel (residue d positive (k + n))),
        ((ambient, residue d positive (k + n)), some false),
        unaryTapes source quotient remainder base 0 ((k + n) / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  induction n generalizing k register with
  | zero =>
    simpa only [Nat.zero_add, Nat.add_zero, Function.iterate_one,
      MachineComposition.advance_some] using
      scanStep_zero d positive source quotient remainder sourceQuotient sourceRemainder
        quotientRemainder scanLabel emitterLabel program atScan base (k / d)
        sourceSuffix quotientSuffix remainderSuffix ambient (residue d positive k) register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (TM2.step program ⟨some scanLabel, ((ambient, residue d positive k), register),
        unaryTapes source quotient remainder base (n + 1) (k / d) 0
          sourceSuffix quotientSuffix remainderSuffix⟩) = _
    rw [scanStep_succ d positive source quotient remainder sourceQuotient sourceRemainder
      quotientRemainder scanLabel emitterLabel program atScan]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) (some true)

theorem emitterWithFinishStep [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K) (emitterLabel : Fin d → Λ) (exit : Option Λ)
    (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n q : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.step program ⟨some (emitterLabel r), ((ambient, r), register),
      unaryTapes source quotient remainder base n q 0
        sourceSuffix quotientSuffix remainderSuffix⟩ =
      some ⟨exit, ((finish ambient r, residue d positive 0), none),
        unaryTapes source quotient remainder base n q r.val
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  change some (TM2.stepAux (program (emitterLabel r)) ((ambient, r), register)
    (unaryTapes source quotient remainder base n q 0
      sourceSuffix quotientSuffix remainderSuffix)) = _
  rw [atEmitter]
  unfold emitterWithFinish
  rw [stepAux_pushWord]
  simp only [unaryTapes, MachineCopy.forkTapes_right, List.reverse_replicate]
  rw [update_remainder]
  cases exit <;>
    simp [TM2.stepAux, Reduction.MachineTransfer.exitAt, encodeWord, List.append_assoc]

theorem divModTraceWithFinish [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register),
        unaryTapes source quotient remainder base n 0 0
          sourceSuffix quotientSuffix remainderSuffix⟩) =
      some ⟨exit, ((finish ambient (residue d positive n), residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hscan := scanTrace_fromCount d positive source quotient remainder
    sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel program atScan
    base n 0 sourceSuffix quotientSuffix remainderSuffix ambient register
  simp only [Nat.zero_add, Nat.zero_div] at hscan
  rw [Function.iterate_succ_apply', hscan, MachineComposition.advance_some]
  exact emitterWithFinishStep d positive source quotient remainder emitterLabel exit finish
    program atEmitter base 0 (n / d) sourceSuffix quotientSuffix remainderSuffix ambient
    (residue d positive n) (some false)

theorem divModFromTapesWithFinish [Fintype σ] (d : Nat) (positive : 0 < d)
    (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (exit : Option Λ) (finish : σ → Fin d → σ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ d))
    (atScan : program scanLabel = scanLoop d positive source quotient scanLabel emitterLabel)
    (atEmitter : ∀ r, program (emitterLabel r) =
      emitterWithFinish d positive remainder exit finish r)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 2]
      (some ⟨some scanLabel, ((ambient, residue d positive 0), register), base⟩) =
      some ⟨exit, ((finish ambient (residue d positive n), residue d positive 0), none),
        unaryTapes source quotient remainder base 0 (n / d) (n % d)
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hbase : unaryTapes source quotient remainder base n 0 0 sourceSuffix quotientSuffix
      remainderSuffix = base := by
    simp only [unaryTapes, ← sourceInput, ← quotientInput, ← remainderInput,
      MachineCopy.forkTapes_self]
  have h := divModTraceWithFinish d positive source quotient remainder sourceQuotient
    sourceRemainder quotientRemainder scanLabel emitterLabel exit finish program atScan
    atEmitter base n sourceSuffix quotientSuffix remainderSuffix ambient register
  rw [hbase] at h
  exact h

end MinUncutGames.Foundations.Complexity.MachineFixedDivMod

namespace MinUncutGames.Foundations.Complexity.MachineExpanderRow

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem transportedDivision {K Λ σ τ : Type} [DecidableEq K] [Fintype σ]
    (q : Nat) (positive : 0 < q) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder)
    (states : MachineFixedDivMod.State σ q ≃ τ)
    (scanLabel : Λ) (emitterLabel : Fin q → Λ) (exit : Option Λ)
    (finish : σ → Fin q → σ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ τ)
    (atScan : target scanLabel = MachineControl.statement id states
      (MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel))
    (atEmitter : ∀ r, target (emitterLabel r) = MachineControl.statement id states
      (MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r))
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base source = encodeWord n ++ sourceSuffix)
    (quotientInput : base quotient = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base remainder = encodeWord 0 ++ remainderSuffix)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some (MachineControl.configuration id states
        ⟨some scanLabel, ((ambient, MachineFixedDivMod.residue q positive 0), register), base⟩)) =
      some (MachineControl.configuration id states
        ⟨exit, ((finish ambient (MachineFixedDivMod.residue q positive n),
          MachineFixedDivMod.residue q positive 0), none),
          MachineFixedDivMod.unaryTapes source quotient remainder base 0 (n / q) (n % q)
            sourceSuffix quotientSuffix remainderSuffix⟩) := by
  let sourceProgram := MachineControl.program (Equiv.refl Λ) states.symm target
  have sourceScan : sourceProgram scanLabel =
      MachineFixedDivMod.scanLoop q positive source quotient scanLabel emitterLabel := by
    change MachineControl.statement id states.symm (target scanLabel) = _
    rw [atScan]
    exact controlStatement_inverse states _
  have sourceEmit : ∀ r, sourceProgram (emitterLabel r) =
      MachineFixedDivMod.emitterWithFinish q positive remainder exit finish r := by
    intro r
    change MachineControl.statement id states.symm (target (emitterLabel r)) = _
    rw [atEmitter]
    exact controlStatement_inverse states _
  have htrace := MachineFixedDivMod.divModFromTapesWithFinish q positive source quotient
    remainder sourceQuotient sourceRemainder quotientRemainder scanLabel emitterLabel exit
    finish sourceProgram sourceScan sourceEmit base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ambient register
  have roundtrip : MachineControl.program (Equiv.refl Λ) states sourceProgram = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatement_inverse states.symm _
  have simulation : ∀ a b, TM2.step sourceProgram a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states sourceProgram a
    rw [roundtrip, hab] at h
    exact h
  exact MachineComposition.liftSuccessfulTrace (TM2.step sourceProgram) (TM2.step target)
    (MachineControl.configuration id states) simulation (n + 2) _ _ htrace

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

theorem firstDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientFirst) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderFirst) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient
        (receiveFirst control (MachineFixedDivMod.residue (degree d)
          (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientFirst .remainderFirst base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientFirst ≠ ports .remainderFirst :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .firstScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientFirst) (labels .firstScan)
        (fun r => labels (.firstResidue r))) := atProgram .firstScan
  have he : ∀ r, target (labels (.firstResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderFirst) (some (labels .clearQuery)) firstFinish r) :=
    fun r => atProgram (.firstResidue r)
  have h := transportedDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientFirst) (ports .remainderFirst) hsq hsr hqr
    (divisionStates ρ d) (labels .firstScan) (fun r => labels (.firstResidue r))
    (some (labels .clearQuery)) firstFinish target hs he base n sourceSuffix quotientSuffix
    remainderSuffix sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, firstFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

theorem secondDivisionTrace {d : Nat} (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (portsInjective : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (atProgram : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool)
    (sourceInput : base (ports .lookupOutput) = encodeWord n ++ sourceSuffix)
    (quotientInput : base (ports .quotientSecond) = encodeWord 0 ++ quotientSuffix)
    (remainderInput : base (ports .remainderSecond) = encodeWord 0 ++ remainderSuffix)
    (ambient : ρ) (control : Control d) (register : Option Bool) :
    (MachineComposition.advance (TM2.step target))^[n + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient control register, base⟩) =
      some ⟨some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient
          (receiveSecond H control (MachineFixedDivMod.residue (degree d)
            (Nat.mul_pos positive positive) n)) none,
        divisionOutput d ports .quotientSecond .remainderSecond base n
          sourceSuffix quotientSuffix remainderSuffix⟩ := by
  have hsq : ports .lookupOutput ≠ ports .quotientSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hsr : ports .lookupOutput ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hqr : ports .quotientSecond ≠ ports .remainderSecond :=
    fun h => Tape.noConfusion (portsInjective h)
  have hs : target (labels .secondScan) = MachineControl.statement id (divisionStates ρ d)
      (MachineFixedDivMod.scanLoop (degree d) (Nat.mul_pos positive positive)
        (ports .lookupOutput) (ports .quotientSecond) (labels .secondScan)
        (fun r => labels (.secondResidue r))) := atProgram .secondScan
  have he : ∀ r, target (labels (.secondResidue r)) =
      MachineControl.statement id (divisionStates ρ d)
        (MachineFixedDivMod.emitterWithFinish (degree d) (Nat.mul_pos positive positive)
          (ports .remainderSecond)
          (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
          (secondFinish H) r) := fun r => atProgram (.secondResidue r)
  have h := transportedDivision (degree d) (Nat.mul_pos positive positive)
    (ports .lookupOutput) (ports .quotientSecond) (ports .remainderSecond) hsq hsr hqr
    (divisionStates ρ d) (labels .secondScan) (fun r => labels (.secondResidue r))
    (some (labels (.outputEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))))
    (secondFinish H) target hs he base n sourceSuffix quotientSuffix remainderSuffix
    sourceInput quotientInput remainderInput ((ambient, control), ()) register
  simpa only [MachineControl.configuration, divisionStates_apply, secondFinish, divisionState,
    divisionOutput, Option.map_some, id_eq] using h

end MinUncutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderTableProgram
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderFamily

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

variable {ρ : Type} [Fintype ρ]

open _root_.Turing

theorem toBoolTapes_eq_transport (base : (tape : Tape) → List (Alphabet tape)) :
    toBoolTapes base = MachineAlphabetTransport.tapes alphabet_eq base := by
  funext tape
  rw [transport_tapes_apply]
  rcases tape with tape | tape
  · cases tape <;> rfl
  · rfl

theorem configuration_toBool {ρ : Type} {d : Nat} (label : Option (Label d))
    (state : State ρ d) (base : (tape : Tape) → List (Alphabet tape)) :
    MachineAlphabetTransport.configuration alphabet_eq ⟨label, state, base⟩ =
      ⟨label, state, toBoolTapes base⟩ := by
  rw [MachineAlphabetTransport.configuration_mk, toBoolTapes_eq_transport]

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

end MinUncutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderFamilyAffine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderRow

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

variable {ρ : Type} [Fintype ρ] {d : Nat}

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

def lookupPhaseLabel {d : Nat} (second : Bool)
    (l : MachinePreservingLookupClean.Label) : Label d :=
  if second then .secondLookup l else .firstLookup l

def scanPhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondScan else .firstScan

def reversePhaseLabel {d : Nat} (second : Bool) : Label d :=
  if second then .secondReverse else .firstReverse

theorem lookupTape_injective : Function.Injective lookupTape := by decide

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

section Reverse

variable {d : Nat} (second : Bool) (positive : 0 < d)
    (H : Table (cloudSize d) d) (ports : Tape → K)
    (distinct : Function.Injective ports) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive H ports labels exit l)
    (base : K → List Bool)
    (ambient : (Ambient ρ d × Fin (degree d)) × Unit) (register : Option Bool)

include positive H distinct exit code

theorem reversePhaseTrace :
    (advance (TM2.step target))^[(base (ports .queryReverse)).length + 1]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          ((base (ports .queryReverse)).reverse ++ base (ports .queryIndex))⟩ := by
  have h := Reduction.MachineTransfer.transferAt_fromTapes
    (ports .queryReverse) (ports .queryIndex)
    (fun h => (by decide : Tape.queryReverse ≠ .queryIndex) (distinct h))
    id false (labels (reversePhaseLabel second))
    (some (labels (lookupPhaseLabel second (.run .copyFirst)))) target
    (by cases second <;> exact code _) base ambient register
  unfold Reduction.MachineTransfer.nextAt at h
  unfold advance
  simpa only [List.map_id] using h

theorem reversePhaseTrace_unary (index : Nat) (suffix : List Bool)
    (queryWord : base (ports .queryReverse) = (encodeWord index).reverse)
    (indexWord : base (ports .queryIndex) = suffix) :
    (advance (TM2.step target))^[index + 2]
      (some ⟨some (labels (reversePhaseLabel second)), (ambient, register), base⟩) =
      some ⟨some (labels (lookupPhaseLabel second (.run .copyFirst))), (ambient, none),
        Reduction.MachineTransfer.tapesAt (ports .queryReverse) (ports .queryIndex) base []
          (encodeWord index ++ suffix)⟩ := by
  have h := reversePhaseTrace second positive H ports distinct labels exit target code
    base ambient register
  simpa only [queryWord, indexWord, List.length_reverse, encodeWord_length,
    List.reverse_reverse, Nat.add_assoc] using h

end Reverse

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K]

def cleanupSteps (ports : Tape → K) (base : K → List Bool) : Nat :=
  ((base (ports .queryIndex)).length + 1) +
  ((base (ports .lookupOutput)).length + 1) +
  ((base (ports .quotientFirst)).length + 1) +
  ((base (ports .quotientSecond)).length + 1) +
  ((base (ports .remainderFirst)).length + 1) +
  ((base (ports .remainderSecond)).length + 1)

variable [Fintype ρ] {d : Nat}

theorem cleanupOneTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (i : Fin 6) (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[((base (ports (dirtyTape i))).length + 1)]
      (some ⟨some (labels (.cleanup i)), state, base⟩) =
      some ⟨some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
          else labels .done),
        (state.1, none), Function.update base (ports (dirtyTape i)) []⟩ := by
  have run := MachineDrain.drainTrace (ports (dirtyTape i)) (labels (.cleanup i))
    (some (if hi : i.val + 1 < 6 then labels (.cleanup ⟨i.val + 1, hi⟩)
      else labels .done)) target
    (by simpa only [statement] using code (.cleanup i))
    base (base (ports (dirtyTape i))) state.1 state.2
  simpa only [Function.update_eq_self] using run

theorem cleanupTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩ := by
  let t1 := Function.update base (ports .queryIndex) []
  let t2 := Function.update t1 (ports .lookupOutput) []
  let t3 := Function.update t2 (ports .quotientFirst) []
  let t4 := Function.update t3 (ports .quotientSecond) []
  let t5 := Function.update t4 (ports .remainderFirst) []
  have h0 := cleanupOneTraceAt positive H ports labels exit target code 0 base state
  have h1 := cleanupOneTraceAt positive H ports labels exit target code 1 t1 (state.1, none)
  have h2 := cleanupOneTraceAt positive H ports labels exit target code 2 t2 (state.1, none)
  have h3 := cleanupOneTraceAt positive H ports labels exit target code 3 t3 (state.1, none)
  have h4 := cleanupOneTraceAt positive H ports labels exit target code 4 t4 (state.1, none)
  have h5 := cleanupOneTraceAt positive H ports labels exit target code 5 t5 (state.1, none)
  simp [t1, t2, t3, t4, t5, distinct.eq_iff,
    -Function.iterate_succ] at h0 h1 h2 h3 h4 h5
  have finished := join_trace (join_trace (join_trace (join_trace (join_trace h0 h1) h2) h3) h4) h5
  simpa only [cleanupSteps, cleanupTapes] using finished

theorem doneStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .done), state, base⟩ = some ⟨exit, state, base⟩ := by
  change some (TM2.stepAux (target (labels .done)) state base) = _
  rw [code]
  cases exit <;> rfl

theorem cleanupExitTraceAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    (advance (TM2.step target))^[cleanupSteps ports base + 1]
      (some ⟨some (labels (.cleanup 0)), state, base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
  have cleaned := cleanupTraceAt positive H ports distinct labels exit target code base state
  have done : (advance (TM2.step target))^[1]
      (some ⟨some (labels .done), (state.1, none), cleanupTapes ports base⟩) =
      some ⟨exit, (state.1, none), cleanupTapes ports base⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      doneStepAt positive H ports labels exit target code (cleanupTapes ports base) (state.1, none)
  exact join_trace cleaned done

theorem initializeStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .initialize_), state, base⟩ =
      some ⟨some (labels (.firstEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        (state.1, none), initializedTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .initialize_)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, initializedTapes, distinct.eq_iff]

theorem clearQueryStepAt (positive : 0 < d) (H : Table (cloudSize d) d)
    (ports : Tape → K) (distinct : Function.Injective ports)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State ρ d))
    (code : ∀ label, target (labels label) = statement positive H ports labels exit label)
    (base : K → List Bool) (state : State ρ d) :
    TM2.step target ⟨some (labels .clearQuery), state, base⟩ =
      some ⟨some (labels (.secondEmit (PCP.AlphabetTable.Emitter.labelAt 3 _ 0 .entry))),
        state, clearedQueryTapes ports base⟩ := by
  change some (TM2.stepAux (target (labels .clearQuery)) state base) = _
  rw [code]
  simp [statement, TM2.stepAux, clearedQueryTapes, distinct.eq_iff]

end MinUncutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderRowFrames
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderRow

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

namespace RowData

variable {v d : Nat} (r : RowData v d)

def tableLength : Nat := (encodeWords (rotationWords r.oldTable)).length

theorem query1_eq_firstRow : r.query1 = r.firstRow.val :=
  firstAddress_eq_rowIndex r.inputVertex r.control0

theorem query2_eq_secondRow : r.query2 = r.secondRow.val :=
  secondAddress_eq_rowIndex r.firstVertex r.control1

theorem firstReturn_eq_residue (positive : 0 < d) :
    r.firstReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.firstValue := Fin.ext rfl

theorem secondReturn_eq_residue (positive : 0 < d) :
    r.secondReturn = MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive)
      r.secondValue := Fin.ext rfl

theorem rows_le_tableLength : v * degree d ≤ r.tableLength := by
  simp only [tableLength, encodeWords_length, rotationWords_length]
  omega

theorem query1_le_tableLength : r.query1 ≤ r.tableLength := by
  rw [query1_eq_firstRow]
  exact r.firstRow.isLt.le.trans r.rows_le_tableLength

theorem query2_le_tableLength : r.query2 ≤ r.tableLength := by
  rw [query2_eq_secondRow]
  exact r.secondRow.isLt.le.trans r.rows_le_tableLength

theorem firstValue_le_tableLength : r.firstValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.firstRow).isLt.le.trans r.rows_le_tableLength

theorem secondValue_le_tableLength : r.secondValue ≤ r.tableLength :=
  (reverseIndex r.oldTable r.secondRow).isLt.le.trans r.rows_le_tableLength

theorem inputVertex_le_tableLength : r.inputVertex.val ≤ r.tableLength := by
  have hq : 1 ≤ degree d := Nat.zero_lt_of_lt r.inputPort.isLt
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  exact r.inputVertex.isLt.le.trans (hv.trans r.rows_le_tableLength)

theorem firstVertex_le_tableLength : r.firstVertex.val ≤ r.tableLength := by
  rw [← firstValue_div_degree]
  exact (Nat.div_le_self r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondVertex_le_tableLength : r.secondVertex.val ≤ r.tableLength := by
  rw [← secondValue_div_degree]
  exact (Nat.div_le_self r.secondValue (degree d)).trans r.secondValue_le_tableLength

theorem firstReturn_le_tableLength : r.firstReturn.val ≤ r.tableLength := by
  rw [← firstValue_mod_degree]
  exact (Nat.mod_le r.firstValue (degree d)).trans r.firstValue_le_tableLength

theorem secondReturn_le_tableLength : r.secondReturn.val ≤ r.tableLength := by
  rw [← secondValue_mod_degree]
  exact (Nat.mod_le r.secondValue (degree d)).trans r.secondValue_le_tableLength

end RowData

variable {v d : Nat}

theorem final_frame_eq (r : RowData v d) (output : List Bool) :
    frame12 r output = emittedWord .output (frame0 r output) r.finalValue := by
  funext tape
  cases tape <;> simp [frame0, emittedWord, frameContents]

theorem cleanupSteps_le_tableLength (r : RowData v d) (output : List Bool) :
    cleanupSteps id (frame11 r output) ≤ 6 * (r.tableLength + 1) + 6 := by
  have h1 := r.firstVertex_le_tableLength
  have h2 := r.secondVertex_le_tableLength
  have h3 := r.firstReturn_le_tableLength
  have h4 := r.secondReturn_le_tableLength
  simp only [cleanupSteps, frame11_eq, id_eq, frameContents, encodeWord_length]
  omega

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

end MinUncutGames.Foundations.Complexity.MachineExpanderRow

namespace MinUncutGames.Foundations.Complexity.MachineExpanderTable

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

theorem nextPosition_val_of_lt (positive : 0 < d) (position : Position d)
    (more : position.val + 1 < rowFactor d) :
    (nextPosition positive position).val = position.val + 1 := Nat.mod_eq_of_lt more

variable [Fintype ρ]

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .initialize_), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetState positive H state,
        Function.update base (.inl .inputVertex) (false :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .initialize_)) state base) = _
  rw [program_outer]
  rfl

theorem vertexGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        Function.update base (.inr .vertexCount) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord, List.replicate_succ]

theorem vertexGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord]

theorem prepareRowStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .prepareRow), state, base⟩ =
      some ⟨some (.inl .initialize_), prepareState positive H state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .prepareRow)) state base) = _
  rw [program_outer]
  rfl

theorem afterRow_moreStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (more : state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .prepareRow), advancePositionState positive state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, more]

theorem afterRow_lastStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        Function.update base (.inl .inputVertex) (true :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, last]

theorem reverseOutput_consStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (symbol : Bool) (word : List Bool) (source : base (.inl .output) = symbol :: word) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
        Function.update (Function.update base (.inl .output) word)
          (.inr .result) (symbol :: base (.inr .result))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, source]

theorem reverseOutput_nilStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (source : base (.inl .output) = []) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have same : Function.update base (.inl .output) [] = base := by
    simpa only [source] using Function.update_eq_self (.inl .output) base
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, clearRegister, source, same]

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .done)) state base) = _
  rw [program_outer]
  rfl

end MinUncutGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ExpanderTableEnumeration
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open MinUncutGames.Foundations.Complexity

variable {v d : Nat}

theorem vertexWords_drop_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) :
    (vertexWords G H vertex).drop position.val =
      rowValue G H vertex position :: (vertexWords G H vertex).drop (position.val + 1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp [vertexWords]

theorem vertexWords_drop_last (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d))
    (last : position.val + 1 = rowFactor d) :
    (vertexWords G H vertex).drop position.val = [rowValue G H vertex position] := by
  rw [vertexWords_drop_succ, last, vertexWords_drop_full]

theorem priorVertices_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (k : Nat) (hk : k < v) :
    priorVertices G H (k + 1) = priorVertices G H k ++ vertexWords G H ⟨k, hk⟩ := by
  unfold priorVertices
  rw [List.take_succ_eq_append_getElem (by simpa using hk), List.flatten_append]
  simp

theorem accumulate_eq (values : List Nat) (initial : List Bool) :
    accumulate values initial = (encodeWords values).reverse ++ initial := by
  induction values generalizing initial with
  | nil => simp [accumulate, encodeWords]
  | cons value values ih =>
      simpa only [accumulate, List.foldl_cons, encodeWords, List.reverse_append,
        List.append_assoc] using ih ((encodeWord value).reverse ++ initial)

theorem accumulate_append (first second : List Nat) (initial : List Bool) :
    accumulate (first ++ second) initial = accumulate second (accumulate first initial) := by
  simp only [accumulate, List.foldl_append]

theorem accumulate_generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (initial : List Bool) :
    accumulate (generatedWords G H) initial =
      (encodeWords (rotationWords (step G H))).reverse ++ initial := by
  rw [accumulate_eq, generatedWords_eq_rotationWords]

theorem encode_generatedWords_length_le (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (encodeWords (generatedWords G H)).length ≤
      (v * rowFactor d) * (v * rowFactor d + 1) := by
  rw [generatedWords_eq_rotationWords, rowCount_eq]
  exact encode_rotationWords_length_le (step G H)

end MinUncutGames.Foundations.PCP.ExpanderTableEnumeration

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderTableRows
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineExpanderTable

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem tableRowData_finalValue {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) :
    (tableRowData G H vertex position).finalValue = rowValue G H vertex position := rfl

variable {ρ : Type} [Fintype ρ] {v d : Nat}

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem accumulatedVertices_succ {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (current : Nat) (valid : current < v) :
    accumulatedVertices G H (current + 1) =
      accumulate (vertexWords G H ⟨current, valid⟩) (accumulatedVertices G H current) := by
  simp only [accumulatedVertices, priorVertices_succ G H current valid, accumulate_append]

theorem accumulatedVertices_full {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) : accumulatedVertices G H v =
      (encodeWords (rotationWords (step G H))).reverse := by
  simp [accumulatedVertices, accumulate_generatedWords]

open _root_.Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

variable [Fintype ρ]

open _root_.Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

theorem vertices_le_word_length {v d : Nat} (positive : 0 < d)
    (G : Table v (degree d)) : v ≤ (oldTableWord G).length := by
  have hq : 1 ≤ degree d := Nat.mul_pos positive positive
  have hv : v ≤ v * degree d := by simpa using Nat.mul_le_mul_left v hq
  have hr : v * degree d ≤ (oldTableWord G).length := by
    simp only [oldTableWord, encodeWords_length, rotationWords_length]
    omega
  exact hv.trans hr

end MinUncutGames.Foundations.Complexity.MachineExpanderTable

namespace MinUncutGames.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem wordLength_add_one_le {v q N : Nat} (G : Table v q) (hv : v ≤ N) :
    (encodeWords (rotationWords G)).length + 1 ≤ (q + 1)^2 * (N + 1)^2 := by
  have hlength := encode_rotationWords_length_le G
  have hrow : v * q + 1 ≤ (q + 1) * (N + 1) := by
    have h := Nat.mul_le_mul_right q hv
    nlinarith
  calc
    _ ≤ (v * q + 1)^2 := by nlinarith
    _ ≤ ((q + 1) * (N + 1))^2 := Nat.pow_le_pow_left hrow 2
    _ = _ := by ring

end MinUncutGames.Foundations.Complexity.MachineExpanderFamilyBounds

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineExpanderFamilyCycle
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamily

open _root_.Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem familyView_right (j : Tape) (tape : MachineExpanderFamily.Tape)
    (h : familyView j = some tape) : familyTape tape = j := by
  cases j with
  | inl j =>
    have hj : j = tape := Option.some.inj h
    subst tape
    rfl
  | inr j => simp [familyView] at h

variable {ρ : Type} [Fintype ρ]

open _root_.Turing
open MachineCloudPadding
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def retainedFrame (requested : Nat) : Tape → List Bool
  | .inl _ => []
  | .inr tape => retainedCeilingTapes requested tape

theorem family_initial_tapes (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = handoffTapes requested := by
  funext tape
  cases tape <;> rfl

theorem family_final_tapes (H : SmallTable) (requested : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes
        (MachineExpanderFamily.familyTapes H (PCP.PreprocessingLevels.boundedLevel requested) []))
      (retainedFrame requested) = finalTapes H requested := by
  funext tape
  cases tape <;> rfl

theorem family_initial_configuration {ρ : Type} (requested : Nat)
    (state : MachineExpanderFamily.State ρ fixedDegree) (metadata : Bool × Option Bool) :
    Placement.configuration familyView familyLabel none (retainedFrame requested)
      (MachineStateFrame.frameConfiguration metadata
        (MachineAlphabetTransport.configuration MachineExpanderFamily.alphabet_eq
          ⟨some (.inr .initialize_), state,
            MachineExpanderFamily.initialTapes (PCP.PreprocessingLevels.boundedLevel requested) []⟩)) =
      ⟨some familyEntry, (state, metadata), handoffTapes requested⟩ := by
  rw [MachineExpanderFamily.configuration_toBool]
  simp only [MachineStateFrame.frameConfiguration, Placement.configuration, Placement.label,
    family_initial_tapes, familyEntry, familyLabel]

theorem finalTapes_currentSize (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape (.inr .currentSize)) =
      encodeWord (PCP.PreprocessingLevels.paddedSize requested) := by
  change encodeWord (vertexCount (degree fixedDegree)
    (PCP.PreprocessingLevels.boundedLevel requested)) = _
  exact congrArg encodeWord (PCP.PreprocessingLevels.table_vertexCount_eq_paddedSize requested)

theorem finalTapes_table (H : SmallTable) (requested : Nat) :
    finalTapes H requested (familyTape MachineExpanderFamily.tableTape) =
      encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel requested))) := rfl

end MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachinePaddedExpanderFamilyBounds
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

theorem ceilingCost_le (g k : Nat) :
    (MachineCeilingPower.timePolynomial g).eval (encodeWord k).length ≤
      (g + 29) * (k + 1)^5 := by
  rw [MachineCeilingPower.timePolynomial_encoding]
  have squareBound : (k + 1)^2 ≤ (k + 1)^5 :=
    Nat.pow_le_pow_right (Nat.succ_pos k) (by decide)
  have linearBound : k + 1 ≤ (k + 1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (Nat.succ_pos k) (show 1 ≤ 5 by decide)
  have constantBound : 1 ≤ (k + 1)^5 := by omega
  have squareCost := Nat.mul_le_mul_left (g + 8) squareBound
  have linearCost := Nat.mul_le_mul_left 18 linearBound
  have constantCost := Nat.mul_le_mul_left 3 constantBound
  unfold MachineCeilingPower.timeBound
  nlinarith only [squareCost, linearCost, constantCost]

end MinUncutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryLessAt

open _root_.Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem scan_step_zero_left (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, decide (0 < b)), none),
        tapes slots base (encodeWord 0 ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  cases b <;> simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_zero_right (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ =
      some ⟨some restoreLabel, ((ambient, false), none),
        tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord 0 ++ rightSuffix) savedLeft savedRight⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, stop, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scan_step_succ (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    TM2.step program ⟨some scanLabel, ((ambient, flag), register),
      tapes slots base (encodeWord (a + 1) ++ leftSuffix) (encodeWord (b + 1) ++ rightSuffix)
        savedLeft savedRight⟩ =
      some ⟨some scanLabel, ((ambient, flag), some true),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix)
          (true :: savedLeft) (true :: savedRight)⟩ := by
  change some (TM2.stepAux (program scanLabel) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, encodeWord, List.replicate_succ]

theorem scanTrace (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atScan : program scanLabel = scan slots scanLabel restoreLabel)
    (base : K → List Bool) (a b : Nat) (leftSuffix rightSuffix savedLeft savedRight : List Bool)
    (ambient : σ) (flag : Bool) (register : Option Bool) :
    (advance (TM2.step program))^[min a b + 1]
      (some ⟨some scanLabel, ((ambient, flag), register),
        tapes slots base (encodeWord a ++ leftSuffix) (encodeWord b ++ rightSuffix) savedLeft savedRight⟩) =
      some ⟨some restoreLabel, ((ambient, decide (a < b)), none),
        tapes slots base (encodeWord (a - b) ++ leftSuffix) (encodeWord (b - a) ++ rightSuffix)
          (List.replicate (min a b) true ++ savedLeft) (List.replicate (min a b) true ++ savedRight)⟩ := by
  induction a generalizing b savedLeft savedRight register with
  | zero =>
    simpa using scan_step_zero_left slots scanLabel restoreLabel program atScan base b
      leftSuffix rightSuffix savedLeft savedRight ambient flag register
  | succ a ih =>
    cases b with
    | zero =>
      simpa using scan_step_zero_right slots scanLabel restoreLabel program atScan base a
        leftSuffix rightSuffix savedLeft savedRight ambient flag register
    | succ b =>
      have hm : min (a + 1) (b + 1) = min a b + 1 := by omega
      rw [hm, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [scan_step_succ slots scanLabel restoreLabel program atScan, ih]
      have hsave (xs : List Bool) :
          List.replicate (min a b) true ++ true :: xs =
            List.replicate (min a b + 1) true ++ xs := by
        simp [List.replicate_add, List.append_assoc]
      simp only [hsave, Nat.add_sub_add_right, Nat.add_lt_add_iff_right]

end MinUncutGames.Foundations.Complexity.MachineUnaryLessAt

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingInternalRows
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.AlphabetGraph.legalDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingInternalRows

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

def destination (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    PaddedCloud t padding v :=
  paddedCloudSelect t padding v (localStep t padding tables v x p).1

theorem cloud_rotation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (cloudGraphs t padding tables v).rot (x, p) =
      (destination t padding tables v x p, (localStep t padding tables v x p).2) := by
  have h := GraphTransport.reindex_rot (ExpanderTables.graph (tables v))
    (paddedCloudEquiv t padding v).symm (Equiv.refl _)
    (paddedCloudRank t padding v x) p
  simpa only [cloudGraphs, ExpanderTables.graph_rot, Equiv.refl_apply,
    paddedCloudRank, paddedCloudSelect, Equiv.symm_apply_apply, destination, localStep] using h

theorem source_rotation (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (sourcePortGraph t padding tables).rot (x.val, .inl p) =
      ((destination t padding tables v x p).val,
        .inl (localStep t padding tables v x p).2) := by
  rcases x with ⟨x, hx⟩
  subst v
  exact congrArg
    (fun z : PaddedCloud t padding
        ((paddedGraph (GraphTables.semantics t) (fun v => Fin (padding v))).tail x) × Fin q =>
      (z.1.val, (Sum.inl z.2 : Fin q ⊕ Unit)))
    (cloud_rotation t padding tables _ ⟨x, rfl⟩ p)

theorem rotation_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    PortTables.rotation (ofCloudTables t padding tables)
        (vertexOrder t padding x.val, portOrder q (.inl p)) =
      (vertexOrder t padding (destination t padding tables v x p).val,
        portOrder q (.inl (localStep t padding tables v x p).2)) := by
  rw [rotation_ofCloudTables, source_rotation t padding tables v x p]

theorem reverseIndex_internal (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    ((ofCloudTables t padding tables).reverseIndex[rowIndex t padding v x p]).val =
      (q + 1) * (vertexOrder t padding (destination t padding tables v x p).val).val +
        (localStep t padding tables v x p).2.val := by
  unfold rowIndex
  rw [← PortTables.rowIndex_rotation, rotation_internal t padding tables v x p,
    PortTables.rowIndex_val, portOrder_internal]
  dsimp only
  omega

theorem row_reverse (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).reverseIndex.val =
      (q + 1) * (vertexOrder t padding (destination t padding tables v x p).val).val +
        (localStep t padding tables v x p).2.val := by
  simpa only [row, PortTables.flatRows, Vector.getElem_ofFn, Fin.getElem_fin] using
    reverseIndex_internal t padding tables v x p

def selectedIndex (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) : Nat :=
  if hi : i.val < cloudSize t v then
    (cloudSelect t v ⟨i.val, hi⟩).val.val
  else t.darts + PreprocessingPaddingOffsets.offset padding v.val + (i.val - cloudSize t v)

theorem selectedIndex_eq (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) :
    (vertexOrder t padding (paddedCloudSelect t padding v i).val).val =
      selectedIndex t padding v i := by
  unfold selectedIndex
  split
  · rename_i hi
    have he : i = Fin.castAdd (padding v) (⟨i.val, hi⟩ : Fin (cloudSize t v)) := Fin.ext rfl
    refine (congrArg (fun j =>
      (vertexOrder t padding (paddedCloudSelect t padding v j).val).val) he).trans ?_
    rw [paddedCloudSelect_castAdd]
    rfl
  · rename_i hi
    have hj : i.val - cloudSize t v < padding v := by have h := i.isLt; omega
    have he : i = Fin.natAdd (cloudSize t v) (⟨i.val - cloudSize t v, hj⟩ : Fin (padding v)) := by
      apply Fin.ext
      dsimp only [Fin.val_natAdd]
      omega
    refine (congrArg (fun j =>
      (vertexOrder t padding (paddedCloudSelect t padding v j).val).val) he).trans ?_
    rw [paddedCloudSelect_natAdd]
    change (vertexOrder t padding
      (Sum.inr ⟨v, (⟨i.val - cloudSize t v, hj⟩ : Fin (padding v))⟩)).val = _
    exact PreprocessingPaddingOffsets.vertexOrder_dummy_val t padding v _

theorem selectedIndex_old (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v))
    (hi : i.val < cloudSize t v) :
    selectedIndex t padding v i = (cloudSelect t v ⟨i.val, hi⟩).val.val := by
  simp only [selectedIndex, dite_eq_left hi]

theorem selectedIndex_dummy (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v))
    (hi : cloudSize t v ≤ i.val) :
    selectedIndex t padding v i =
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + (i.val - cloudSize t v) := by
  simp only [selectedIndex, dite_eq_right (Nat.not_lt_of_ge hi)]

theorem row_reverse_selectedIndex (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (row t padding tables v x p).reverseIndex.val =
      (q + 1) * selectedIndex t padding v (localStep t padding tables v x p).1 +
        (localStep t padding tables v x p).2.val := by
  rw [row_reverse]
  unfold destination
  rw [selectedIndex_eq]

end MinUncutGames.Foundations.PCP.PreprocessingInternalRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Alphabet
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularInternalRow

open _root_.Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ σ : Type} [DecidableEq K]

theorem selected_rotation {n q : Nat} (table : ExpanderTables.Table n q)
    (i : Fin n) (p : Fin q) :
    (ExpanderTableWords.rotationWords table)[q * i.val + p.val]? =
      some (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val) := by
  simpa only [Nat.add_comm] using ExpanderTableWords.rotationWords_row_order table (i, p)

theorem selected_rotation_div {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) / q =
        (ExpanderTables.lookup table (i, p)).1.val := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ positive,
    Nat.div_eq_of_lt (ExpanderTables.lookup table (i, p)).2.isLt, Nat.zero_add]

theorem selected_rotation_mod {n q : Nat} (_positive : 0 < q)
    (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q) :
    (q * (ExpanderTables.lookup table (i, p)).1.val +
      (ExpanderTables.lookup table (i, p)).2.val) % q =
        (ExpanderTables.lookup table (i, p)).2.val := by
  rw [Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt (ExpanderTables.lookup table (i, p)).2.isLt]

def rotorFinalTapes {n q : Nat} (table : ExpanderTables.Table n q) (i : Fin n) (p : Fin q)
    (tape : Fin 8 → K) (base : K → List Bool) : K → List Bool :=
  MachineFixedDivMod.unaryTapes (tape 4) (tape 6) (tape 7)
    (MachineAffineLookup.finalTapes (rotorLookupTapes tape) base
      (ExpanderTableWords.rotationWords table) (q * i.val + p.val)
      (q * (ExpanderTables.lookup table (i, p)).1.val +
        (ExpanderTables.lookup table (i, p)).2.val))
    0 (ExpanderTables.lookup table (i, p)).1.val
      (ExpanderTables.lookup table (i, p)).2.val [] [] []

end MinUncutGames.Foundations.Complexity.MachineRegularInternalRow
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineDummyRows
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularDummyRow

open _root_.Turing MachineComposition PCP.GraphTables

structure Input (x : Nat) (base : Tape → List Bool) : Prop where
  source : base 0 = encodeWord x
  reverseEmpty : base 1 = []
  relationEmpty : base 2 = []
  scratchEmpty : base 3 = []
  rowEmpty : base 5 = []

def memory (x : Nat) (output : List Bool) : Tape → List Bool :=
  ![encodeWord x, [], [], [], output, []]

theorem memory_input (x : Nat) (output : List Bool) : Input x (memory x output) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end MinUncutGames.Foundations.Complexity.MachineRegularDummyRow

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachinePortReindex
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachinePortReindex

open _root_.Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (d : Nat) := MachineFixedDivMod.State A d

def clean (d : Nat) (positive : 0 < d) (ambient : A) : State A d :=
  ((ambient, MachineFixedDivMod.residue d positive 0), none)

def exitAt {divisor : Nat} (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A divisor) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def emit (d : Nat) (positive : 0 < d) (output : K) (b : Nat)
    (r : Fin d) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A d) :=
  pushWord output (List.replicate (r.val + b) true)
    (.load (fun s => clean d positive s.1.1) (.goto fun _ => next))

def instruction (d : Nat) (positive : 0 < d) (c b : Nat)
    (tape : Fin 5 → K) (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (Alphabet (K := K)) Λ (State A d)
  | .copySeed => MachineUnaryAffineAt.seed (tape 2) 0 (labels .copyScan)
  | .copyScan => MachineUnaryAffineAt.scan (tape 0) (tape 1) (tape 2) 1
      (labels .copyScan) (labels .copyRestore)
  | .copyRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 0) id false
      (labels .copyRestore) (some (labels .initialize_))
  | .initialize_ => .push (tape 3) (fun _ => false)
      (.push (tape 4) (fun _ => false) (.goto fun _ => labels .divide))
  | .divide => MachineFixedDivMod.scanLoop d positive (tape 2) (tape 3)
      (labels .divide) (fun r => labels (.emit r))
  | .emit r => emit d positive (tape 4) b r (labels .affineScan)
  | .affineScan => MachineUnaryAffineAt.scan (tape 3) (tape 1) (tape 4) c
      (labels .affineScan) (labels .affineRestore)
  | .affineRestore => Reduction.MachineTransfer.loopAt (tape 1) (tape 3) id false
      (labels .affineRestore) (some (labels .drainQuotient))
  | .drainQuotient => MachineDrain.drain (tape 3) (labels .drainQuotient)
      (some (labels .finish))
  | .finish => .pop (tape 2) (fun s _ => clean d positive s.1.1) (exitAt exit)

end MinUncutGames.Foundations.Complexity.MachinePortReindex

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingLazyWords
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open MinUncutGames.Foundations.Complexity

variable {n d : Nat}

def row (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * d) :=
  ⟨v, table.reverseIndex[rowIndex n d (v, p)], table.relations[rowIndex n d (v, p)]⟩

def stayRow (d : Nat) (v : Fin n) (p : Fin d) : DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) (v, lazyPorts d (false, p)), trueRelation⟩

def moveRow (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    DartRow n (n * (2 * d)) :=
  ⟨v, rowIndex n (2 * d) ((rotation table (v, p)).1,
    lazyPorts d (true, (rotation table (v, p)).2)),
    table.relations[rowIndex n d (v, p)]⟩

theorem row_lazy_stay (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (false, p)) = stayRow d v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      rowIndex n (2 * d) (v, lazyPorts d (false, p)) := by
    rw [← rowIndex_rotation, lazy_rotation_false]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (false, p))] =
      trueRelation := by
    apply relation_ext
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation, Fin.getElem_fin,
      Vector.getElem_replicate] using lazy_accepts_false table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_lazy_move (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    row (lazy table) v (lazyPorts d (true, p)) = moveRow table v p := by
  have hr : (lazy table).reverseIndex[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      rowIndex n (2 * d) ((rotation table (v, p)).1,
        lazyPorts d (true, (rotation table (v, p)).2)) := by
    rw [← rowIndex_rotation, lazy_rotation_true]
  have hp : (lazy table).relations[rowIndex n (2 * d) (v, lazyPorts d (true, p))] =
      table.relations[rowIndex n d (v, p)] := by
    apply relation_ext
    intro a b
    exact lazy_accepts_true table v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem stayRow_reverse_val (v : Fin n) (p : Fin d) :
    (stayRow d v p).reverseIndex.val = 2 * d * v.val + p.val := by
  simp only [stayRow, rowIndex_val, lazyPorts_false_val]
  omega

theorem moveRow_reverse_val (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (moveRow table v p).reverseIndex.val =
      reverseMap d (row table v p).reverseIndex.val := by
  simp only [moveRow, rowIndex_val, lazyPorts_true_val, reverseMap, row]
  change (table.reverseIndex[rowIndex n d (v, p)]).val % d + d +
      (2 * d) * ((table.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem moveRow_words (table : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (moveRow table v p) =
      [v.val, reverseMap d (row table v p).reverseIndex.val] ++
        relationWords (row table v p).relation := by
  rw [rowWords, moveRow_reverse_val]
  rfl

theorem flatRows_list (table : PortTables.Table n d) :
    (flatRows table).toList =
      (List.ofFn fun v : Fin n => List.ofFn (row table v)).flatten := by
  rw [flatRows, Vector.toList_ofFn, ofFn_rowIndex]
  simp only [Equiv.symm_apply_apply]
  rfl

theorem ofFn_lazyPorts {α : Type*} (f : Fin (2 * d) → α) :
    List.ofFn f = List.ofFn (fun p => f (lazyPorts d (false, p))) ++
      List.ofFn (fun p => f (lazyPorts d (true, p))) := by
  have hf (p : Fin d) : rowIndex 2 d (0, p) = lazyPorts d (false, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_zero, Nat.mul_zero, Nat.add_zero, lazyPorts_false_val]
  have ht (p : Fin d) : rowIndex 2 d ((0 : Fin 1).succ, p) = lazyPorts d (true, p) := by
    apply Fin.ext
    simp only [rowIndex_val, Fin.val_succ, Fin.val_zero, Nat.zero_add,
      Nat.mul_one, lazyPorts_true_val]
  simpa only [List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil, hf, ht] using (ofFn_rowIndex (n := 2) (d := d) f)

def vertexRows (table : PortTables.Table n d) (v : Fin n) :
    List (DartRow n (n * (2 * d))) :=
  List.ofFn (stayRow d v) ++ List.ofFn (moveRow table v)

theorem flatRows_lazy (table : PortTables.Table n d) :
    (flatRows (lazy table)).toList = (List.ofFn (vertexRows table)).flatten := by
  rw [flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_lazyPorts]
  simp only [row_lazy_stay, row_lazy_move]
  rfl

theorem tableWords_lazy (table : PortTables.Table n d) :
    PortTables.tableWords (lazy table) =
      [n, n * (2 * d)] ++ (List.ofFn (vertexRows table)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_lazy]

theorem tableBits_lazy (table : PortTables.Table n d) :
    PortTables.tableBits (lazy table) =
      encodeWords ([n, n * (2 * d)] ++
        (List.ofFn (vertexRows table)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (lazy table)) = _
  rw [tableWords_lazy]

end MinUncutGames.Foundations.PCP.PreprocessingLazyWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLazyRows
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLazyRows

open _root_.Turing MachineComposition PCP.GraphTables
open PCP.PreprocessingLazyWords (reverseMap moveRow moveRow_words)

variable {K Λ A : Type} [DecidableEq K]

abbrev State (A : Type) (d : Nat) := MachinePortReindex.State A d

def reindexInstruction (d : Nat) (positive : 0 < d) (c b : Nat) (tape : Fin 9 → K)
    (labels : Label d → Λ) (exit : Option Λ) :
    Label d → TM2.Stmt (fun _ : K => Bool) Λ (State A d)
  | .inl stage => MachinePortReindex.instruction d positive c b
      (tape ∘ addressIndex) (fun stage => labels (.inl stage))
      (some (labels (.inr .relationRead))) stage
  | .inr stage => MachineTableRows.routine (fields tape) (tape 8) (tape 7) (tape 3)
      (fun stage => labels (.inr stage)) exit stage

def reindexRowBits (d c b v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (MachinePortReindex.value d c b j) ++
    encodeWords (relationWords relation)

def reindexMappedTapes (d c b j : Nat) (tape : Fin 9 → K)
    (base : K → List Bool) : K → List Bool :=
  Function.update base (tape 6) (encodeWord (MachinePortReindex.value d c b j))

def reindexResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 9 → K) (base : K → List Bool) : K → List Bool :=
  Function.update (reindexMappedTapes d c b j tape base) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

def reindexSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  MachinePortReindex.steps d j + 4 * (reindexRowBits d c b v j relation).length +
    2 * output.length + 9

def rowBits (d v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord (reverseMap d j) ++ encodeWords (relationWords relation)

theorem rowBits_eq_moveRow {n d : Nat} (table : PCP.PortTables.Table n d)
    (v : Fin n) (p : Fin d) :
    rowBits d v.val (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
        (PCP.PreprocessingLazyWords.row table v p).relation =
      encodeWords (rowWords (moveRow table v p)) := by
  rw [moveRow_words]
  simp [rowBits, encodeWords]

def inputRowBits (v j : Nat) (relation : RelationTable) : List Bool :=
  encodeWord v ++ encodeWord j ++ encodeWords (relationWords relation)

def streamRowSteps (d c b v j : Nat) (relation : RelationTable) (output : List Bool) : Nat :=
  (v + 2) + (j + 2) + 1 + reindexSteps d c b v j relation output +
    (v + 2) + (j + 2) + ((encodeWords (relationWords relation)).length + 1) +
    (MachinePortReindex.value d c b j + 2)

def streamResultTapes (d c b v j : Nat) (relation : RelationTable)
    (tape : Fin 10 → K) (base : K → List Bool) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ reindexRowBits d c b v j relation)

def recordsInput {n m : Nat} (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => inputRowBits r.tail.val r.reverseIndex.val r.relation)

def recordsOutput {n m : Nat} (d c b : Nat) (rows : List (DartRow n m)) : List Bool :=
  rows.flatMap (fun r => reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

def streamFrame {n m : Nat} (tape : Fin 10 → K) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) (recordsInput rows ++ base (tape 9)))
    (tape 7) output

def vertexSteps {n m : Nat} (d c b : Nat) : List (DartRow n m) → List Bool → Nat
  | [], _ => 1
  | r :: rows, output => 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
      vertexSteps d c b rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation)

theorem recordsInput_eq_codec {n m : Nat} (rows : List (DartRow n m)) :
    recordsInput rows = encodeWords (rows.flatMap rowWords) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
      simp only [recordsInput, List.flatMap_cons, encodeWords_append,
        MachineTableRows.rowBits_eq, inputRowBits] at ih ⊢
      rw [ih]

theorem streamFrame_afterRow {n m : Nat} (d c b : Nat) (r : DartRow n m)
    (tape : Fin 10 → K) (distinct : Function.Injective tape) (base : K → List Bool)
    (rows : List (DartRow n m)) (output : List Bool) :
    streamResultTapes d c b r.tail.val r.reverseIndex.val r.relation tape
      (streamFrame tape base (r :: rows) output) (recordsInput rows ++ base (tape 9)) =
      streamFrame tape base rows
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [streamResultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [streamResultTapes, streamFrame, Ne.symm h79]
    · simp [streamResultTapes, streamFrame, h7, h9]

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem recordsOutput_lazy {n d : Nat} (table : PCP.PortTables.Table n d) (v : Fin n) :
    recordsOutput d (2 * d) d (List.ofFn (PCP.PreprocessingLazyWords.row table v)) =
      encodeWords ((List.ofFn (moveRow table v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [recordsOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  change reindexRowBits d (2 * d) d v.val
      (PCP.PreprocessingLazyWords.row table v p).reverseIndex.val
      (PCP.PreprocessingLazyWords.row table v p).relation =
    encodeWords (rowWords (moveRow table v p))
  have h := rowBits_eq_moveRow table v p
  simpa only [rowBits, reindexRowBits, MachinePortReindex.lazy_value, reverseMap] using h

theorem reindexValue_le {n m : Nat} (d c b : Nat) (r : DartRow n m) :
    MachinePortReindex.value d c b r.reverseIndex.val ≤ valueBound c b m := by
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hmod := (Nat.mod_le r.reverseIndex.val d).trans hj
  have hmul := Nat.mul_le_mul_left c hdiv
  unfold MachinePortReindex.value valueBound
  omega

theorem reindexRowBits_length_le {n m : Nat} (d c b : Nat) (r : DartRow n m) :
    (reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length ≤
      rowSizeBound c b n m := by
  have htail := r.tail.isLt.le
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  simp only [reindexRowBits, List.length_append, encodeWord_length]
  unfold rowSizeBound
  omega

theorem streamRowSteps_le {n m : Nat} (d c b : Nat) (r : DartRow n m) (output : List Bool) :
    streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output ≤
      rowCostBound c b n m + 2 * output.length := by
  have htail := r.tail.isLt.le
  have hj := r.reverseIndex.isLt.le
  have hdiv := (Nat.div_le_self r.reverseIndex.val d).trans hj
  have hvalue := reindexValue_le d c b r
  have hrelation := relationBits_length_le r.relation
  have hsize := reindexRowBits_length_le d c b r
  unfold streamRowSteps reindexSteps MachinePortReindex.steps rowCostBound
  omega

theorem vertexSteps_le_capacity {n m : Nat} (d c b capacity : Nat)
    (rows : List (DartRow n m)) (output : List Bool)
    (room : output.length + rows.length * rowSizeBound c b n m ≤ capacity) :
    vertexSteps d c b rows output ≤
      rows.length * (rowCostBound c b n m + 2 * capacity + 1) + 1 := by
  induction rows generalizing output with
  | nil => simp [vertexSteps]
  | cons r rows ih =>
      have hsize := reindexRowBits_length_le d c b r
      have hcost := streamRowSteps_le d c b r output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation).length +
          rows.length * rowSizeBound c b n m ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih
        (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) hroom
      change 1 + streamRowSteps d c b r.tail.val r.reverseIndex.val r.relation output +
        vertexSteps d c b rows
          (output ++ reindexRowBits d c b r.tail.val r.reverseIndex.val r.relation) ≤
        (rows.length + 1) * (rowCostBound c b n m + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem vertexSteps_le {n m : Nat} (d c b : Nat) (rows : List (DartRow n m))
    (output : List Bool) :
    vertexSteps d c b rows output ≤ rows.length * (rowCostBound c b n m +
      2 * (output.length + rows.length * rowSizeBound c b n m) + 1) + 1 :=
  vertexSteps_le_capacity d c b _ rows output (Nat.le_refl _)

end MinUncutGames.Foundations.Complexity.MachineLazyRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingOverlayWords
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingOverlayWords

open PortTables GraphTables PreprocessingOverlayTables
open Complexity

variable {n d e : Nat}

abbrev row := @PreprocessingLazyWords.row

def oldRow (G : PortTables.Table n d) (e : Nat) (v : Fin n) (p : Fin d) :
    DartRow n (n * (d + e)) :=
  ⟨v, rowIndex n (d + e) ((rotation G (v, p)).1,
    overlayPorts d e (.inl (rotation G (v, p)).2)),
    G.relations[rowIndex n d (v, p)]⟩

def expanderRow (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    DartRow n (n * (d + e)) :=
  ⟨v, rowIndex n (d + e) ((ExpanderTables.lookup H (v, p)).1,
    overlayPorts d e (.inr (ExpanderTables.lookup H (v, p)).2)), trueRelation⟩

theorem row_overlay_old (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin d) :
    row (overlay G H) v (overlayPorts d e (.inl p)) = oldRow G e v p := by
  have hr : (overlay G H).reverseIndex[rowIndex n (d + e) (v, overlayPorts d e (.inl p))] =
      rowIndex n (d + e) ((rotation G (v, p)).1,
        overlayPorts d e (.inl (rotation G (v, p)).2)) := by
    rw [← rowIndex_rotation, overlay_rotation_old]
  have hp : (overlay G H).relations[rowIndex n (d + e) (v, overlayPorts d e (.inl p))] =
      G.relations[rowIndex n d (v, p)] := by
    apply relation_ext
    exact overlay_accepts_old G H v p
  exact congrArg₂ (DartRow.mk v) hr hp

theorem row_overlay_expander (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    row (overlay G H) v (overlayPorts d e (.inr p)) = expanderRow d H v p := by
  have hr : (overlay G H).reverseIndex[rowIndex n (d + e) (v, overlayPorts d e (.inr p))] =
      rowIndex n (d + e) ((ExpanderTables.lookup H (v, p)).1,
        overlayPorts d e (.inr (ExpanderTables.lookup H (v, p)).2)) := by
    rw [← rowIndex_rotation, overlay_rotation_expander]
  have hp : (overlay G H).relations[rowIndex n (d + e) (v, overlayPorts d e (.inr p))] =
      trueRelation := by
    apply relation_ext
    intro a b
    simpa only [PortTables.accepts, relationAt, trueRelation,
      PreprocessingLazyWords.trueRelation, Fin.getElem_fin, Vector.getElem_replicate] using
      overlay_accepts_expander G H v p a b
  exact congrArg₂ (DartRow.mk v) hr hp

theorem oldRow_reverse_val (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    (oldRow G e v p).reverseIndex.val = oldReverseMap d e (row G v p).reverseIndex.val := by
  simp only [oldRow, rowIndex_val, overlayPorts_inl_val, oldReverseMap, row,
    PreprocessingLazyWords.row]
  change (G.reverseIndex[rowIndex n d (v, p)]).val % d +
      (d + e) * ((G.reverseIndex[rowIndex n d (v, p)]).val / d) = _
  omega

theorem expanderRow_reverse_val (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    (expanderRow d H v p).reverseIndex.val =
      expanderReverseMap d e (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val := by
  simp only [expanderRow, rowIndex_val, overlayPorts_inr_val, expanderReverseMap]
  change d + (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val % e +
      (d + e) * ((ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val / e) = _
  omega

theorem oldRow_words (G : PortTables.Table n d) (v : Fin n) (p : Fin d) :
    rowWords (oldRow G e v p) =
      [v.val, oldReverseMap d e (row G v p).reverseIndex.val] ++
        relationWords (row G v p).relation := by
  rw [rowWords, oldRow_reverse_val]
  rfl

theorem expanderRow_words (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) :
    rowWords (expanderRow d H v p) =
      [v.val, expanderReverseMap d e
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++
        List.replicate 4096 1 := by
  rw [rowWords, expanderRow_reverse_val]
  exact congrArg (fun rs => [v.val, expanderReverseMap d e
    (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val] ++ rs)
      PreprocessingLazyWords.relationWords_true

theorem ofFn_overlayPorts {α : Type*} (f : Fin (d + e) → α) :
    List.ofFn f = List.ofFn (fun p => f (overlayPorts d e (.inl p))) ++
      List.ofFn (fun p => f (overlayPorts d e (.inr p))) := by
  rw [List.ofFn_add]
  rfl

def vertexRows (G : PortTables.Table n d) (H : ExpanderTables.Table n e) (v : Fin n) :
    List (DartRow n (n * (d + e))) :=
  List.ofFn (oldRow G e v) ++ List.ofFn (expanderRow d H v)

theorem flatRows_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    (flatRows (overlay G H)).toList = (List.ofFn (vertexRows G H)).flatten := by
  rw [PreprocessingLazyWords.flatRows_list]
  apply congrArg List.flatten
  congr 1
  funext v
  rw [ofFn_overlayPorts]
  simp only [row_overlay_old, row_overlay_expander]
  rfl

theorem tableWords_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableWords (overlay G H) =
      [n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords := by
  rw [PortTables.tableWords_eq, flatRows_overlay]

theorem tableBits_overlay (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.tableBits (overlay G H) = encodeWords
      ([n, n * (d + e)] ++ (List.ofFn (vertexRows G H)).flatten.flatMap rowWords) := by
  change encodeWords (PortTables.tableWords (overlay G H)) = _
  rw [tableWords_overlay]

theorem rotationWords_vertices (H : ExpanderTables.Table n e) :
    ExpanderTableWords.rotationWords H =
      (List.ofFn fun v : Fin n => List.ofFn fun p : Fin e =>
        (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val).flatten := by
  have hflat : ExpanderTableWords.rotationWords H =
      List.ofFn (fun i : Fin (n * e) => (ExpanderTables.reverseIndex H i).val) := by
    apply List.ext_getElem
    · simp [ExpanderTableWords.rotationWords_length]
    · intro i hi hj
      rw [ExpanderTableWords.rotationWords_getElem H i (by simpa using hi)]
      simp only [List.getElem_ofFn]
  rw [hflat, PreprocessingLazyWords.ofFn_rowIndex]
  rfl

end MinUncutGames.Foundations.PCP.PreprocessingOverlayWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineOverlayRows
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineOverlayRows

open _root_.Turing MachineComposition
open PCP.GraphTables PCP.PreprocessingOverlayWords
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]
variable {e : Nat}

abbrev State (A : Type) (e : Nat) := MachinePortReindex.State A e

def trueBits : List Bool := encodeWords (relationWords trueRelation)

def instruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : Label e → Λ) (exit : Option Λ) :
    Label e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | .loadStart => Hastad.SourceMachine.fieldStart (tape 1) (labels .loadLoop)
  | .loadLoop => Hastad.SourceMachine.fieldLoop (tape 9) (tape 1)
      (labels .loadLoop) (some (labels .seedRelation))
  | .seedRelation => pushWord (tape 2) trueBits.reverse
      (.goto fun _ => labels (.row (.inl .copySeed)))
  | .row stage => MachineLazyRows.reindexInstruction e positive (d + e) d
      (tape ∘ bodyIndex) (fun stage => labels (.row stage))
      (some (labels .drainOld)) stage
  | .drainOld => MachineDrain.drain (tape 1) (labels .drainOld) (some (labels .drainNew))
  | .drainNew => MachineDrain.drain (tape 6) (labels .drainNew) (some (labels .drainRelation))
  | .drainRelation => MachineDrain.drain (tape 2) (labels .drainRelation) exit

def rowBits (d e v j : Nat) : List Bool :=
  MachineLazyRows.reindexRowBits e (d + e) d v j trueRelation

def rowSteps (d e v j : Nat) (output : List Bool) : Nat :=
  (j + 2) + 1 + MachineLazyRows.reindexSteps e (d + e) d v j trueRelation output +
    (j + 2) + (MachinePortReindex.value e (d + e) d j + 2) + (trueBits.length + 1)

def resultTapes (d e v j : Nat) (tape : Fin 10 → K) (base : K → List Bool)
    (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) suffix) (tape 7)
    (base (tape 7) ++ rowBits d e v j)

theorem rowBits_eq_expanderRow {n : Nat} (d : Nat) (H : PCP.ExpanderTables.Table n e)
    (v : Fin n) (p : Fin e) :
    rowBits d e v.val (PCP.ExpanderTables.reverseIndex H
        (PCP.ExpanderTables.rowIndex n e (v, p))).val =
      encodeWords (rowWords (expanderRow d H v p)) := by
  rw [expanderRow_words]
  have h (j : Nat) : MachinePortReindex.value e (d + e) d j = expanderReverseMap d e j := by
    unfold MachinePortReindex.value expanderReverseMap
    omega
  simp only [rowBits, MachineLazyRows.reindexRowBits, h,
    PCP.PreprocessingLazyWords.relationWords_true, List.cons_append,
    List.nil_append, encodeWords, List.append_assoc]

def vertexInstruction (d e : Nat) (positive : 0 < e) (tape : Fin 10 → K)
    (labels : VertexLabel e → Λ) (exit : Option Λ) :
    VertexLabel e → TM2.Stmt (fun _ : K => Bool) Λ (State A e)
  | (i, none) => if i.val < e then .goto fun _ => labels (i, some .loadStart)
      else MachinePortReindex.exitAt exit
  | (i, some stage) => if h : i.val < e then
      instruction d e positive tape (fun stage => labels (i, some stage))
        (some (labels (⟨i.val + 1, by omega⟩, none))) stage
      else MachinePortReindex.exitAt exit

def streamFrame (tape : Fin 10 → K) (base : K → List Bool)
    (words : List Nat) (output : List Bool) : K → List Bool :=
  Function.update (Function.update base (tape 9) (encodeWords words ++ base (tape 9)))
    (tape 7) output

def streamOutput (d e v : Nat) (words : List Nat) : List Bool :=
  words.flatMap (rowBits d e v)

def vertexSteps (d e v : Nat) : List Nat → List Bool → Nat
  | [], _ => 1
  | j :: words, output => 1 + rowSteps d e v j output +
      vertexSteps d e v words (output ++ rowBits d e v j)

def rowSizeBound (d e v B : Nat) : Nat := v + valueBound d e B + trueBits.length + 2
def rowCostBound (d e v B : Nat) : Nat :=
  8 * B + 4 * rowSizeBound d e v B + valueBound d e B + trueBits.length + 28

theorem rowBits_length (d e v j : Nat) :
    (rowBits d e v j).length = v + MachinePortReindex.value e (d + e) d j + trueBits.length + 2 := by
  simp only [rowBits, MachineLazyRows.reindexRowBits, List.length_append, encodeWord_length,
    trueBits]
  omega

theorem rowBits_length_le (d e v j B : Nat) (hj : j ≤ B) :
    (rowBits d e v j).length ≤ rowSizeBound d e v B := by
  rw [rowBits_length]
  have h := value_le d e j B hj
  unfold rowSizeBound
  omega

theorem rowSteps_le (d e v j B : Nat) (hj : j ≤ B) (output : List Bool) :
    rowSteps d e v j output ≤ rowCostBound d e v B + 2 * output.length := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hval := value_le d e j B hj
  have hsize := rowBits_length_le d e v j B hj
  change (MachineLazyRows.reindexRowBits e (d + e) d v j trueRelation).length ≤
    rowSizeBound d e v B at hsize
  unfold rowSteps MachineLazyRows.reindexSteps MachinePortReindex.steps rowCostBound
  omega

theorem vertexSteps_le_capacity (d e v B capacity : Nat)
    (words : List Nat) (bounded : ∀ j ∈ words, j ≤ B) (output : List Bool)
    (room : output.length + words.length * rowSizeBound d e v B ≤ capacity) :
    vertexSteps d e v words output ≤
      words.length * (rowCostBound d e v B + 2 * capacity + 1) + 1 := by
  induction words generalizing output with
  | nil => simp [vertexSteps]
  | cons j words ih =>
      have hj := bounded j (by simp)
      have hb : ∀ k ∈ words, k ≤ B := fun k hk => bounded k (by simp [hk])
      have hsize := rowBits_length_le d e v j B hj
      have hcost := rowSteps_le d e v j B hj output
      have hout : output.length ≤ capacity := by omega
      have hroom : (output ++ rowBits d e v j).length +
          words.length * rowSizeBound d e v B ≤ capacity := by
        rw [List.length_append]
        simp only [List.length_cons, Nat.succ_mul] at room
        omega
      have htail := ih hb (output ++ rowBits d e v j) hroom
      change 1 + rowSteps d e v j output +
        vertexSteps d e v words (output ++ rowBits d e v j) ≤
        (words.length + 1) * (rowCostBound d e v B + 2 * capacity + 1) + 1
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem vertexSteps_le (d e v B : Nat) (words : List Nat)
    (bounded : ∀ j ∈ words, j ≤ B) (output : List Bool) :
    vertexSteps d e v words output ≤
      words.length * (rowCostBound d e v B +
        2 * (output.length + words.length * rowSizeBound d e v B) + 1) + 1 :=
  vertexSteps_le_capacity d e v B _ words bounded output (Nat.le_refl _)

theorem streamFrame_afterRow (d e v j : Nat) (tape : Fin 10 → K)
    (distinct : Function.Injective tape) (base : K → List Bool)
    (words : List Nat) (output : List Bool) :
    resultTapes d e v j tape (streamFrame tape base (j :: words) output)
      (encodeWords words ++ base (tape 9)) =
      streamFrame tape base words (output ++ rowBits d e v j) := by
  have h79 : tape 7 ≠ tape 9 := fun h => (by decide : (7 : Fin 10) ≠ 9) (distinct h)
  funext k
  by_cases h7 : k = tape 7
  · subst k
    simp [resultTapes, streamFrame]
  · by_cases h9 : k = tape 9
    · subst k
      simp [resultTapes, streamFrame, Ne.symm h79]
    · simp [resultTapes, streamFrame, h7, h9]

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem streamOutput_expanderRows {n : Nat} (d : Nat) (H : PCP.ExpanderTables.Table n e)
    (v : Fin n) :
    streamOutput d e v.val (List.ofFn fun p : Fin e =>
      (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).val) =
      encodeWords ((List.ofFn (expanderRow d H v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [streamOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  exact rowBits_eq_expanderRow d H v p

theorem expanderValues_bounded {n : Nat} (H : PCP.ExpanderTables.Table n e) (v : Fin n)
    (p : Fin e) :
    (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).val ≤ n * e :=
  (PCP.ExpanderTables.reverseIndex H (PCP.ExpanderTables.rowIndex n e (v, p))).isLt.le

end MinUncutGames.Foundations.Complexity.MachineOverlayRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularMetadata
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularMetadata

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP


variable {σ : Type}

theorem selected_owner (t : GraphTables.Table) (e : Fin t.darts) :
    (GraphTables.tableWords t)[4098 * e.val + 2]? = some t.rows[e].tail.val := by
  have h := congrArg (fun words : List Nat => words[0]?)
    (MachineRegularOriginalRow.tableWords_drop_row t e)
  simp only [List.getElem?_drop, Nat.add_zero] at h
  rw [show 2 + 4098 * e.val = 4098 * e.val + 2 by omega] at h
  simpa [GraphTables.rowWords] using h

theorem encodeWords_drop_length_le (values : List Nat) (n : Nat) :
    (encodeWords (values.drop n)).length ≤ (encodeWords values).length := by
  have h := congrArg (fun words : List Nat => (encodeWords words).length)
    (List.take_append_drop n values)
  simp only [encodeWords_append, List.length_append] at h
  omega

end MinUncutGames.Foundations.Complexity.MachineRegularMetadata

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_SelectorMachine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularInternalRow
open _root_.Turing MachineComposition
open PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)
variable {K Λ σ : Type} [DecidableEq K]

theorem selectedIndex_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (PreprocessingCloudIndex.cloudSize t v + padding v)) :
    PreprocessingInternalRows.selectedIndex t padding v i ≤
      t.darts + PreprocessingPaddingOffsets.offset padding v.val + i.val := by
  unfold PreprocessingInternalRows.selectedIndex
  split
  · rename_i hi
    have h := (PreprocessingCloudIndex.cloudSelect t v ⟨i.val, hi⟩).val.isLt
    omega
  · omega

theorem encodedDrop_length_le (values : List Nat) (n : Nat) :
    (encodeWords (values.drop n)).length ≤ (encodeWords values).length := by
  have h : (encodeWords (values.take n)).length + (encodeWords (values.drop n)).length =
      (encodeWords values).length := by
    rw [← List.length_append, ← encodeWords_append, List.take_append_drop]
  omega

theorem rotorSize_le_encodedLength {n q : Nat} (positive : 0 < q)
    (table : ExpanderTables.Table n q) :
    n ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
  have h : n * q ≤ (encodeWords (ExpanderTableWords.rotationWords table)).length := by
    rw [encodeWords_length, ExpanderTableWords.rotationWords_length]
    omega
  exact (Nat.le_mul_of_pos_right n positive).trans h

end MinUncutGames.Foundations.Complexity.MachineRegularInternalRow

end
section
namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalClean

open _root_.Turing MachineComposition PCP PCP.GraphTables PCP.PreprocessingRegularTables

structure Input (t : Table) (e : Fin t.darts) (base : Tape → List Bool) : Prop
    extends MachineRegularOriginalRow.Input t e base where
  queryEmpty : base 2 = []
  scanEmpty : base 3 = []

theorem cleanup_frame (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupTapes (MachineRegularOriginalRow.finalTapes q t e base) =
      Function.update base 9
        (base 9 ++ encodeWords (MachineRegularOriginalRow.emittedWords q t e)) := by
  funext k
  fin_cases k <;>
    simp [cleanupTapes, MachineRegularOriginalRow.finalTapes,
      MachineRegularOriginalRow.affined, MachineRegularOriginalRow.copied,
      MachineRegularOriginalRow.looked, MachineAffineLookup.finalTapes,
      MachinePreservingLookup.finalTapes, MachineLookup.tapes,
      MachineRegularOriginalRow.lookupTape, input.queryEmpty, input.scanEmpty,
      input.reverseEmpty, input.computedEmpty, input.relationEmpty]

theorem suffix_length_le (t : Table) (e : Fin t.darts) :
    (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length ≤ (tableBits t).length := by
  have hlength : (tableBits t).length =
      (encodeWords (MachineRegularOriginalRow.prefixWords t e)).length +
        ((encodeWords (rowWords t.rows[e])).length +
          (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length) := by
    rw [tableBits, MachineRegularOriginalRow.tableWords_at_row,
      encodeWords_append, encodeWords_append, List.length_append, List.length_append]
  omega

theorem cleanupSteps_eq (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) =
      (encodeWords (MachineRegularOriginalRow.suffixWords t e)).length +
        (q + 2) * t.rows[e].reverseIndex.val + q +
          (encodeWords (relationWords t.rows[e].relation)).length + 8 := by
  have hquery : MachineRegularOriginalRow.finalTapes q t e base 2 = encodeWord 0 := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 6), MachineRegularOriginalRow.copied,
      Function.update_of_ne (by decide : (2 : Tape) ≠ 7),
      Function.update_of_ne (by decide : (2 : Tape) ≠ 3)]
    change MachineLookup.tapes (2 : Tape) 3 4 base
      (encodeWord 0 ++ base 2)
      (encodeWords ((GraphTables.tableWords t).drop (4098 * e.val + 3 + 1)) ++ base 3)
      (encodeWord t.rows[e].reverseIndex.val ++ base 4) 2 = _
    rw [MachineLookup.tapes_index _ _ _ (by decide) (by decide), input.queryEmpty,
      List.append_nil]
  have hscan : MachineRegularOriginalRow.finalTapes q t e base 3 =
      encodeWords (MachineRegularOriginalRow.suffixWords t e) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 6), MachineRegularOriginalRow.copied,
      Function.update_of_ne (by decide : (3 : Tape) ≠ 7), Function.update_self,
      input.scanEmpty, List.append_nil]
  have hraw : MachineRegularOriginalRow.finalTapes q t e base 4 =
      encodeWord t.rows[e].reverseIndex.val := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (4 : Tape) ≠ 9), MachineRegularOriginalRow.affined,
      Function.update_of_ne (by decide : (4 : Tape) ≠ 6), MachineRegularOriginalRow.copied_reverse,
      input.reverseEmpty, List.append_nil]
  have hcomputed : MachineRegularOriginalRow.finalTapes q t e base 6 =
      encodeWord ((q + 1) * t.rows[e].reverseIndex.val + q) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (6 : Tape) ≠ 9), MachineRegularOriginalRow.affined_reverse,
      input.computedEmpty, List.append_nil]
  have hrelation : MachineRegularOriginalRow.finalTapes q t e base 7 =
      encodeWords (relationWords t.rows[e].relation) := by
    simp only [MachineRegularOriginalRow.finalTapes,
      Function.update_of_ne (by decide : (7 : Tape) ≠ 9), MachineRegularOriginalRow.affined_relation,
      input.relationEmpty, List.append_nil]
  simp only [cleanupSteps, hquery, hscan, hraw, hcomputed, hrelation, encodeWord_length]
  ring

theorem cleanupSteps_le (q : Nat) (t : Table) (e : Fin t.darts)
    (base : Tape → List Bool) (input : Input t e base) :
    cleanupSteps (MachineRegularOriginalRow.finalTapes q t e base) ≤
      (q + 3) * (tableBits t).length + q + 8200 := by
  rw [cleanupSteps_eq q t e base input]
  have hsuffix := suffix_length_le t e
  have htable := tableWords_length_le_bits t
  have hr : t.rows[e].reverseIndex.val ≤ (tableBits t).length := by
    have hrlt := t.rows[e].reverseIndex.isLt
    omega
  have hmul := Nat.mul_le_mul_left (q + 2) hr
  have hrel := relationBits_length_le t.rows[e].relation
  nlinarith

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalClean

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingPaddingWords
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

def rowsBits (table : Table n d) : List Bool :=
  encodeWords ((flatRows table).toList.flatMap GraphTables.rowWords)

theorem rowBits_flat (table : Table n d) (i : Fin (n * d)) :
    encodeWords (GraphTables.rowWords ((flatRows table)[i])) =
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2 := by
  simp only [flatRows, Vector.getElem_ofFn, Fin.getElem_fin,
    MachineTableRows.rowBits_eq, rowBits, Prod.eta, Equiv.apply_symm_apply]

theorem rowsBits_eq_vertices (table : Table n d) :
    rowsBits table = (List.ofFn (fun v : Fin n => vertexBits table v)).flatten := by
  have hflat : (flatRows table).toList =
      List.ofFn (fun i : Fin (n * d) => (flatRows table)[i]) := by
    simp only [flatRows, Vector.toList_ofFn, Vector.getElem_ofFn, Fin.getElem_fin]
  unfold rowsBits
  rw [hflat, encodeWords_flatMap, List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun i : Fin (n * d) =>
    encodeWords (GraphTables.rowWords ((flatRows table)[i])))).flatten = _
  simp_rw [rowBits_flat]
  simpa only [Equiv.symm_apply_apply, vertexBits] using
    flatten_ofFn_rowIndex (fun i : Fin (n * d) =>
      rowBits table ((rowIndex n d).symm i).1 ((rowIndex n d).symm i).2)

end MinUncutGames.Foundations.PCP.PreprocessingPaddingWords

end
section
namespace MinUncutGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

theorem inherited_original_words (e : Fin t.darts) :
    GraphTables.rowWords (actualRow t padding tables (.inl e) (.inr ())) =
      [e.val, (q + 1) * t.rows[e].reverseIndex.val + q] ++
        GraphTables.relationWords t.rows[e].relation := by
  simp only [GraphTables.rowWords, actualRow_tail, vertexOrder_original,
    inherited_original_reverse, inherited_original_relation]

theorem inherited_dummy_words (v : Fin t.vertices) (j : Fin (padding v)) :
    GraphTables.rowWords (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())) =
      [t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val,
        (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q] ++
        GraphTables.relationWords MachineDummyRows.trueRelation := by
  simp only [GraphTables.rowWords, actualRow_tail,
    PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    inherited_dummy_reverse, inherited_dummy_relation]

theorem encodeWords_flatMap {α : Type*} (xs : List α) (words : α → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem actualRow_bits (x : Vertex t padding) (p : Fin q ⊕ Unit) :
    encodeWords (GraphTables.rowWords (actualRow t padding tables x p)) =
      PreprocessingPaddingWords.rowBits (ofCloudTables t padding tables)
        (vertexOrder t padding x) (portOrder q p) := by
  simpa only [actualRow, Equiv.symm_apply_apply] using
    PreprocessingPaddingWords.rowBits_flat (ofCloudTables t padding tables)
      (PortTables.rowIndex _ _ (vertexOrder t padding x, portOrder q p))

theorem paddingOrder_ofFn :
    List.ofFn (paddingOrder padding).symm = paddingList padding := by
  calc
    List.ofFn (paddingOrder padding).symm =
        List.ofFn (fun i : Fin (paddingList padding).length =>
          (paddingOrder padding).symm (Fin.cast (paddingList_length padding) i)) :=
      List.ofFn_congr (paddingList_length padding).symm (paddingOrder padding).symm
    _ = paddingList padding := by
      change List.ofFn (fun i => (paddingList padding).get i) = _
      exact List.ofFn_get _


theorem vertexOrder_ofFn {α : Type*} (f : Vertex t padding → α) :
    List.ofFn (fun i : Fin (vertexCount t padding) => f ((vertexOrder t padding).symm i)) =
      List.ofFn (fun e : Fin t.darts => f (.inl e)) ++
        (paddingList padding).map (fun z => f (.inr z)) := by
  change List.ofFn (fun i : Fin (t.darts + ∑ v, padding v) =>
    f ((vertexOrder t padding).symm i)) = _
  rw [List.ofFn_add]
  have hold (e : Fin t.darts) :
      (vertexOrder t padding).symm (e.castLE (Nat.le_add_right t.darts (∑ v, padding v))) =
        Sum.inl e := (vertexOrder t padding).symm_apply_apply (Sum.inl e)
  have hnew (i : Fin (∑ v, padding v)) :
      (vertexOrder t padding).symm (i.natAdd t.darts) =
        Sum.inr ((paddingOrder padding).symm i) := by
    apply (vertexOrder t padding).injective
    erw [Equiv.apply_symm_apply]
    change i.natAdd t.darts = Fin.natAdd t.darts
      ((paddingOrder padding) ((paddingOrder padding).symm i))
    rw [Equiv.apply_symm_apply]
  apply congrArg₂ (· ++ ·)
  · exact congrArg List.ofFn (funext (fun i => congrArg f (hold i)))
  · calc
      List.ofFn (fun i : Fin (∑ v, padding v) =>
          f ((vertexOrder t padding).symm (i.natAdd t.darts))) =
          List.ofFn (fun i => f (.inr ((paddingOrder padding).symm i))) :=
        congrArg List.ofFn (funext (fun i => congrArg f (hnew i)))
      _ = (List.ofFn (paddingOrder padding).symm).map (fun z => f (.inr z)) :=
        (List.map_ofFn (f := (paddingOrder padding).symm) (g := fun z => f (.inr z))).symm
      _ = _ := by rw [paddingOrder_ofFn]


theorem paddingList_flatMap {α : Type*} (f : (Σ v : Fin t.vertices, Fin (padding v)) → List α) :
    (paddingList padding).flatMap f =
      (List.ofFn (fun v : Fin t.vertices =>
        (List.ofFn (fun j : Fin (padding v) => f ⟨v, j⟩)).flatten)).flatten := by
  simp only [paddingList, List.sigma, List.finRange, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

end MinUncutGames.Foundations.PCP.PreprocessingRegularWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularVertexBlock
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineRegularVertexBlock

open _root_.Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

def rowBits (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) : List Bool :=
  encodeWords (GraphTables.rowWords (PreprocessingInternalRows.row t padding tables v x p))

def originalMemory (graph : List Bool) (x : Nat) (output : List Bool) :
    MachineRegularOriginalClean.Tape → List Bool :=
  ![encodeWord x, graph, [], [], [], [], [], [], [], output]

theorem originalMemory_input (t : GraphTables.Table) (e : Fin t.darts) (output : List Bool) :
    MachineRegularOriginalClean.Input t e (originalMemory (GraphTables.tableBits t) e.val output) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

theorem originalMemory_update (graph : List Bool) (x : Nat) (output output' : List Bool) :
    Function.update (originalMemory graph x output) (9 : MachineRegularOriginalClean.Tape) output' =
      originalMemory graph x output' := by funext j; fin_cases j <;> rfl

theorem dummyMemory_update (x : Nat) (output output' : List Bool) :
    Function.update (MachineRegularDummyRow.memory x output)
      (4 : MachineRegularDummyRow.Tape) output' = MachineRegularDummyRow.memory x output' := by
  funext j; fin_cases j <;> rfl

def oldCloud (t : GraphTables.Table) (padding : Fin t.vertices → Nat) (e : Fin t.darts) :
    PaddedCloud t padding t.rows[e].tail := paddedOld t padding t.rows[e].tail ⟨e, rfl⟩

theorem encodeWords_flatMap {A : Type*} (xs : List A) (words : A → List Nat) :
    encodeWords (xs.flatMap words) = xs.flatMap (fun x => encodeWords (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem encodeWords_pair (a b : Nat) (rest : List Nat) :
    encodeWords ([a, b] ++ rest) = encodeWord a ++ (encodeWord b ++ encodeWords rest) := rfl

theorem rowBits_length_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) (p : Fin q) :
    (rowBits t padding tables v x p).length ≤ rowSizeBound q (vertexCount t padding) :=
  GraphTables.rowBits_length_le _

theorem allRowBits_length_le (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)
    (v : Fin t.vertices) (x : PaddedCloud t padding v) :
    (List.ofFn (rowBits t padding tables v x)).flatten.length ≤
      q * rowSizeBound q (vertexCount t padding) := by
  rw [← portBits_all]
  exact portBits_length_le _ _ (rowBits_length_le t padding tables v x) q

end MinUncutGames.Foundations.Complexity.MachineRegularVertexBlock

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingFamilyBridge
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingFamilyBridge

open PreprocessingCloudIndex PreprocessingRegularTables ExpanderTableWords
open MinUncutGames.Foundations.Complexity (encodeWords)

theorem rotationWords_resizeTable {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) :
    rotationWords (resizeTable h table) = rotationWords table := by
  cases h
  rfl

end MinUncutGames.Foundations.PCP.PreprocessingFamilyBridge

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularOriginalBody
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalBody

open _root_.Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable

def vertexView : Tape → Option (Fin 27)
  | .inl i => some i
  | .inr _ => none

theorem vertexView_left (k : Fin 27) : vertexView (.inl k) = some k := rfl

theorem vertexView_right (j : Tape) (k : Fin 27)
    (h : vertexView j = some k) : Sum.inl k = j := by
  cases j with
  | inl i => cases h; rfl
  | inr e => cases h

theorem identityPlacement (base extra : Tape → List Bool) :
    MachineCloudPadding.Placement.tapes some base extra = base := rfl

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalBody

namespace MinUncutGames.Foundations.Complexity.MachineRegularOwnerCleanup

open _root_.Turing MachineComposition

variable {LabelType : Type}

def steps (base : Tape → List Bool) (d : Nat) : Nat :=
  2 * (d + 1) + (cleanupTapes.map (fun k => (base k).length + 1)).sum

theorem drainSteps_eq (base : Tape → List Bool) (d o : Nat) :
    MachineDrainMany.steps cleanupTapes (afterAddition base d o) =
      (cleanupTapes.map (fun k => (base k).length + 1)).sum := by
  simp [MachineDrainMany.steps, cleanupTapes, afterAddition, prefixTape,
    localRank, count, rotor, padding, level, dummyFuel, core]

end MinUncutGames.Foundations.Complexity.MachineRegularOwnerCleanup

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOwnerBody

open _root_.Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable
open PreprocessingRegularLoopWords

def initialData (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) : Data where
  table := GraphTables.tableBits t
  globalIndex := encodeWord (t.darts + PreprocessingPaddingOffsets.offset (padding t) v.val)
  owner := encodeWord v.val
  localRank := []
  count := []
  offset := encodeWord (PreprocessingPaddingOffsets.offset (padding t) v.val)
  darts := encodeWord t.darts
  rotor := []
  output := output
  padding := []
  level := []

open _root_.Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

def preSteps (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (2 * (cloudSize t v + 1) + 1) +
    (2 * (padding t v + 1) + 1)

end MinUncutGames.Foundations.Complexity.MachineRegularOwnerBody

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PreprocessingMachineBounds
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open MinUncutGames.Foundations.Complexity
open scoped BigOperators

theorem cloudRotorBits_le (t : GraphTables.Table) (v : Fin t.vertices) {q : Nat}
    (table : ExpanderTables.Table (cloudSize t v + padding t v) q) :
    (encodeWords (ExpanderTableWords.rotationWords table)).length ≤
      (rotorPolynomial q).eval (inputLength t) := by
  have hd : (cloudSize t v + padding t v) * q ≤
      (ExpanderFamily.growth * q) * inputLength t := by
    calc
      _ ≤ (ExpanderFamily.growth * inputLength t) * q :=
        Nat.mul_le_mul_right _ (cloudTotal_le_input t v)
      _ = _ := by ac_rfl
  have h := (ExpanderTableWords.encode_rotationWords_length_le table).trans
    (Nat.mul_le_mul hd (Nat.add_le_add_right hd 1))
  simpa only [rotorPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using h

end MinUncutGames.Foundations.PCP.PreprocessingMachineBounds

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingRegularBounds
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open MinUncutGames.Foundations.Complexity
open scoped BigOperators

theorem offset_succ {n : Nat} (p : Fin n → Nat) (k : Nat) (h : k < n) :
    PreprocessingPaddingOffsets.offset p (k + 1) =
      PreprocessingPaddingOffsets.offset p k + p ⟨k, h⟩ := by
  unfold PreprocessingPaddingOffsets.offset
  rw [List.take_succ_eq_append_getElem (show k < (List.finRange n).length by simpa using h)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.finRange, List.getElem_ofFn]

def header (t : GraphTables.Table) (p : Fin t.vertices → Nat) (q : Nat) : List Bool :=
  encodeWords [vertexCount t p, vertexCount t p * (q + 1)]

end MinUncutGames.Foundations.PCP.PreprocessingRegularBounds

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularTableTrace
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

open _root_.Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

end MinUncutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

namespace MinUncutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

open _root_.Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

def bodySize (t : GraphTables.Table) (output : List Bool) : Nat :=
  inputLength t + output.length

theorem wide_le (t : GraphTables.Table) (output : List Bool) :
    inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    ExpanderFamily.growth*inputLength t ≤ (ExpanderFamily.growth+1)*bodySize t output ∧
    output.length ≤ (ExpanderFamily.growth+1)*bodySize t output := by
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hO : output.length ≤ bodySize t output := Nat.le_add_left _ _
  have hg := Nat.mul_le_mul_left ExpanderFamily.growth hN
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem preSteps_le (t : GraphTables.Table) (v : Fin t.vertices) (output : List Bool) :
    MachineRegularOwnerBody.preSteps t v ≤ prePolynomial.eval (bodySize t output) := by
  have bounds := wide_le t output
  have hk := cloudSize_le_input t v
  have hd := cloudTotal_le_input t v
  have hv := v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  change v.val ≤ inputLength t at hv
  have hN : inputLength t ≤ bodySize t output := Nat.le_add_right _ _
  have hinput : MachineCloudPadding.inputLength t v [] ≤ 2*bodySize t output+1 := by
    simp only [MachineCloudPadding.inputLength, List.append_nil, encodeWord_length]
    change inputLength t + (v.val+1) ≤ _
    omega
  have hm := (MachineCloudPadding.totalTime_le t v []).trans
    (natPolynomial_eval_mono MachineCloudPadding.timePolynomial hinput)
  simp only [MachineRegularOwnerBody.preSteps, prePolynomial, wide, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one]
  omega

end MinUncutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_PreprocessingStageMaps
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

def padding (d : Nat) (input : PortTables.Input d) : PortTables.Input d :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingPaddingTables.pad input.2 (PreprocessingLevels.le_paddedSize input.1)⟩

def familyAt (H : BaseTable) (n : Nat) :
    ExpanderTables.Table (PreprocessingLevels.paddedSize n) internalDegree :=
  resizeTable (PreprocessingLevels.table_vertexCount_eq_paddedSize n)
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n))

def paddedOverlay (H : BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (d + internalDegree) :=
  ⟨PreprocessingLevels.paddedSize input.1,
    PreprocessingOverlayTables.overlay (padding d input).2 (familyAt H input.1)⟩

def lazy (d : Nat) (input : PortTables.Input d) : PortTables.Input (2 * d) :=
  ⟨input.1, PreprocessingOverlayTables.lazy input.2⟩

end MinUncutGames.Foundations.PCP.PreprocessingStageMaps

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularTableRuntime
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineTableSplit

open _root_.Turing MachineComposition


def program {σ : Type} : Label → TM2.Stmt (fun _ : Tape => Bool) Label (State σ)
  | .copyFirst => Reduction.MachineTransfer.loopAt 0 2 id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop 2 0 1 false .copySecond (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart 3 .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop 1 3 .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart 4 .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop 1 4 .readDarts none

def exactSteps (n m : Nat) (rowsBits : List Bool) : Nat :=
  2 * (encodeWords [n, m] ++ rowsBits).length + n + m + 6

theorem splitTrace {σ : Type} (n m : Nat) (rowsBits : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps n m rowsBits]
      (some ⟨some .copyFirst, (ambient, register),
        initialTapes (encodeWords [n, m] ++ rowsBits)⟩) =
      some ⟨none, (ambient, none), resultTapes n m rowsBits⟩ := by
  let word := encodeWords [n, m] ++ rowsBits
  let b₀ := initialTapes word
  let b₁ := tapes word word [] []
  let b₂ := tapes word (encodeWord m ++ rowsBits) (encodeWord n) []
  let b₃ := resultTapes n m rowsBits
  have h₀ : Function.update b₀ (1 : Tape) (b₀ 0 ++ b₀ 1) = b₁ := by
    funext k; fin_cases k <;> simp [b₀, b₁, initialTapes, tapes]
  have h₁ : Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁
      (encodeWord m ++ rowsBits) (encodeWord n ++ b₁ 3) = b₂ := by
    funext k; fin_cases k <;> simp [b₁, b₂, tapes, Hastad.SourceMachine.fieldTapes]
  have h₂ : Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂
      rowsBits (encodeWord m ++ b₂ 4) = b₃ := by
    funext k; fin_cases k <;>
      simp [b₂, b₃, resultTapes, tapes, word, Hastad.SourceMachine.fieldTapes]
  have copy := MachineCopy.copyTrace (0 : Tape) 1 2
    (by decide) (by decide) (by decide) false .copyFirst .copySecond (some .startVertices)
    (program (σ := σ)) rfl rfl b₀ (by simp [b₀, initialTapes, tapes]) ambient register
  rw [h₀] at copy
  have c₀ : (advance (TM2.step (program (σ := σ))))^[2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startVertices, (ambient, none), b₁⟩ := by
    simpa only [show b₀ 0 = word by simp [b₀, initialTapes, tapes]] using copy
  have scan₁ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 3 (by decide)
    .startVertices .readVertices (some .startDarts) (program (σ := σ)) rfl rfl
    b₁ n (encodeWord m ++ rowsBits)
    (by simp [b₁, tapes, word, encodeWords, List.append_assoc]) ambient none).evals_in_steps
  have c₁ : (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₁
    change (advance (TM2.step (program (σ := σ))))^[n + 2]
      (some ⟨some .startVertices, (ambient, none), b₁⟩) =
      some ⟨some .startDarts, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 3 b₁ (encodeWord m ++ rowsBits)
          (encodeWord n ++ b₁ 3)⟩ at scan₁
    simpa only [h₁] using scan₁
  have scan₂ := (Hastad.SourceMachine.fieldInTime (1 : Tape) 4 (by decide)
    .startDarts .readDarts none (program (σ := σ)) rfl rfl
    b₂ m rowsBits (by simp [b₂, tapes]) ambient none).evals_in_steps
  have c₂ : (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    dsimp only [Hastad.SourceMachine.fieldInTime] at scan₂
    change (advance (TM2.step (program (σ := σ))))^[m + 2]
      (some ⟨some .startDarts, (ambient, none), b₂⟩) =
      some ⟨none, (ambient, none),
        Hastad.SourceMachine.fieldTapes (1 : Tape) 4 b₂ rowsBits
          (encodeWord m ++ b₂ 4)⟩ at scan₂
    simpa only [h₂] using scan₂
  have c₀₁ : (advance (TM2.step (program (σ := σ))))^[(n + 2) + 2 * (word.length + 1)]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨some .startDarts, (ambient, none), b₂⟩ := by
    rw [Function.iterate_add_apply, c₀, c₁]
  have c₀₁₂ : (advance (TM2.step (program (σ := σ))))^[(m + 2) +
      ((n + 2) + 2 * (word.length + 1))]
      (some ⟨some .copyFirst, (ambient, register), b₀⟩) =
        some ⟨none, (ambient, none), b₃⟩ := by
    rw [Function.iterate_add_apply, c₀₁, c₂]
  have count : exactSteps n m rowsBits = (m + 2) + ((n + 2) + 2 * (word.length + 1)) := by
    dsimp [exactSteps, word]
    omega
  rw [count]
  exact c₀₁₂

theorem exactSteps_le (n m : Nat) (rowsBits : List Bool) :
    exactSteps n m rowsBits ≤ timePolynomial.eval (encodeWords [n, m] ++ rowsBits).length := by
  rw [timePolynomial_eval]
  simp only [exactSteps, List.length_append, encodeWords_length, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil]
  omega

def rowsBits (table : PCP.GraphTables.Table) : List Bool :=
  encodeWords ((PCP.GraphTables.rowList table).flatMap PCP.GraphTables.rowWords)

theorem tableBits_header_rows (table : PCP.GraphTables.Table) :
    PCP.GraphTables.tableBits table = encodeWords [table.vertices, table.darts] ++ rowsBits table := by
  simp only [PCP.GraphTables.tableBits, PCP.GraphTables.tableWords, encodeWords_append, rowsBits]

theorem tableTrace {σ : Type} (table : PCP.GraphTables.Table) (ambient : σ)
    (register : Option Bool) :
    (advance (TM2.step (program (σ := σ))))^[exactSteps table.vertices table.darts (rowsBits table)]
      (some ⟨some .copyFirst, (ambient, register), initialTapes (PCP.GraphTables.tableBits table)⟩) =
      some ⟨none, (ambient, none), resultTapes table.vertices table.darts (rowsBits table)⟩ := by
  rw [tableBits_header_rows]
  exact splitTrace table.vertices table.darts (rowsBits table) ambient register

end MinUncutGames.Foundations.Complexity.MachineTableSplit

end
section
namespace MinUncutGames.Foundations.Complexity.MachinePaddingBounds

def inputSize (v e count : Nat) (output : List Bool) : Nat :=
  (encodeWord v).length + (encodeWord e).length + (encodeWord count).length + output.length

theorem rowBound_le_cap (d v e count : Nat) (output : List Bool) :
    rowBound d v e count ≤ rowCap d (inputSize v e count output) := by
  have hbase : v + e + count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hcount : count ≤ inputSize v e count output := by
    simp only [inputSize, encodeWord_length]
    omega
  have hmul := Nat.mul_le_mul_right d (Nat.succ_le_succ hcount)
  have h := Nat.add_le_add_right (Nat.add_le_add hbase hmul) 8194
  simpa only [rowBound, rowCap, Nat.succ_eq_add_one, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using h

end MinUncutGames.Foundations.Complexity.MachinePaddingBounds

end
section
namespace MinUncutGames.Foundations.Complexity.MachinePaddingTable

open PCP MachinePaddingRows

def initialOutput {n d m : Nat} (table : PortTables.Table n d) : List Bool :=
  encodeWords [m, m * d] ++ PreprocessingPaddingWords.rowsBits table

end MinUncutGames.Foundations.Complexity.MachinePaddingTable

end
section
namespace MinUncutGames.Foundations.Complexity.MachineVertexPadding

open _root_.Turing MachineComposition
open MinUncutGames.Foundations.PCP
open MachineCloudPadding


inductive Label (d : Nat)
  | splitCode (l : MachineTableSplit.Label)
  | powerCode (l : MachineCeilingPower.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | copyFirst | copySecond | subtractCode (l : MachineCloudPadding.Label)
  | rowsCode (l : MachinePaddingRows.Label d)
  | cleanVertex | cleanEdge | cleanPower | cleanRelation | cleanFuel
  deriving DecidableEq, Fintype

def splitTape : MachineTableSplit.Tape → Tape := ![.original, .output, .scratch, .vertex, .edge]
def splitView : Tape → Option MachineTableSplit.Tape
  | .original => some 0
  | .output => some 1
  | .scratch => some 2
  | .vertex => some 3
  | .edge => some 4
  | _ => none

theorem splitView_left (k : MachineTableSplit.Tape) : splitView (splitTape k) = some k := by
  fin_cases k <;> rfl
theorem splitView_right (j : Tape) (k : MachineTableSplit.Tape)
    (h : splitView j = some k) : splitTape k = j := by
  cases j <;> fin_cases k <;> simp_all [splitView, splitTape]

def powerTape : MachineCeilingPower.Tape → Tape
  | .input => .vertex
  | .work => .work
  | .power => .power
  | .saved => .saved
  | .level => .level
  | .fuel => .fuel
  | .spare => .scratch
  | .product => .product
def powerView : Tape → Option MachineCeilingPower.Tape
  | .vertex => some .input
  | .work => some .work
  | .power => some .power
  | .saved => some .saved
  | .level => some .level
  | .fuel => some .fuel
  | .scratch => some .spare
  | .product => some .product
  | _ => none

theorem powerView_left (k : MachineCeilingPower.Tape) : powerView (powerTape k) = some k := by
  cases k <;> rfl
theorem powerView_right (j : Tape) (k : MachineCeilingPower.Tape)
    (h : powerView j = some k) : powerTape k = j := by
  cases j <;> cases k <;> simp_all [powerView, powerTape]

theorem tableBits_split {n d : Nat} (t : PortTables.Table n d) :
    PortTables.tableBits t = encodeWords [n, n * d] ++ PreprocessingPaddingWords.rowsBits t := by
  change encodeWords (PortTables.tableWords t) = _
  rw [PortTables.tableWords_eq, encodeWords_append]
  rfl

theorem splitInitialTapes (word : List Bool) :
    Placement.tapes splitView (MachineTableSplit.initialTapes word) (fun _ => []) =
      memory word [] [] [] [] [] [] [] := by
  funext k; cases k <;> simp [Placement.tapes, splitView, MachineTableSplit.initialTapes,
    MachineTableSplit.tapes, memory]

theorem splitResultTapes (n e : Nat) (rows : List Bool) :
    Placement.tapes splitView (MachineTableSplit.resultTapes n e rows) (fun _ => []) =
      memory (encodeWords [n, e] ++ rows) rows (encodeWord n) (encodeWord e) [] [] [] [] := by
  funext k; cases k <;> simp [Placement.tapes, splitView, MachineTableSplit.resultTapes,
    MachineTableSplit.tapes, memory]

theorem powerTapes (input output vertex edge power level : List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory vertex [] power [] level [] [] [])
      (memory input output [] edge [] [] [] []) = memory input output vertex edge power level [] [] := by
  funext k; cases k <;> rfl

def otherTime {n d : Nat} (t : PortTables.Table n d) : Nat :=
  MachineTableSplit.exactSteps n (n * d) (PreprocessingPaddingWords.rowsBits t) +
    MachineCeilingPower.totalTime ExpanderFamily.growth n +
    (4 * (PreprocessingLevels.paddedSize n + 1) + 2) +
    (2 * (PreprocessingLevels.paddedSize n + 2)) + (2 * n + 2) +
    cleanupTime d (PreprocessingLevels.paddedSize n)

theorem rows_length_le {n d : Nat} (t : PortTables.Table n d) :
    (PreprocessingPaddingWords.rowsBits t).length ≤ (PortTables.tableBits t).length := by
  rw [tableBits_split, List.length_append]
  omega

theorem darts_length_le {n d : Nat} (t : PortTables.Table n d) :
    n * d ≤ (PortTables.tableBits t).length :=
  GraphTables.darts_le_tableBits_length (PortTables.graphTable t)

theorem power_length_bound {n d : Nat} (t : PortTables.Table n d) :
    PreprocessingLevels.paddedSize n ≤ ExpanderFamily.growth * ((PortTables.tableBits t).length + 1) :=
  (MachineCeilingPower.paddingOutput_bounds n).2.2.trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (PortTables.vertices_le_tableBits_length t) 1))

theorem initialOutput_length {n d m : Nat} (t : PortTables.Table n d) :
    (MachinePaddingTable.initialOutput (m := m) t).length =
      m + m * d + 2 + (PreprocessingPaddingWords.rowsBits t).length := by
  simp only [MachinePaddingTable.initialOutput, List.length_append, encodeWords_length,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  omega

theorem intermediate_bound {n d : Nat} (t : PortTables.Table n d) :
    MachinePaddingBounds.inputSize n (n * d) (PreprocessingLevels.paddedSize n - n)
      (MachinePaddingTable.initialOutput (m := PreprocessingLevels.paddedSize n) t) ≤
      (intermediatePolynomial d).eval (PortTables.tableBits t).length := by
  have hn := PortTables.vertices_le_tableBits_length t
  have he := darts_length_le t
  have hr := rows_length_le t
  have hm := power_length_bound t
  have hs := Nat.sub_le (PreprocessingLevels.paddedSize n) n
  have hmul := Nat.mul_le_mul_left (d + 2) hm
  simp only [MachinePaddingBounds.inputSize, encodeWord_length, initialOutput_length,
    intermediatePolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, intermediateCoefficient]
  nlinarith

theorem otherTime_le {n d : Nat} (t : PortTables.Table n d) :
    otherTime t ≤ (otherPolynomial d).eval (PortTables.tableBits t).length := by
  have hs := MachineTableSplit.exactSteps_le n (n * d) (PreprocessingPaddingWords.rowsBits t)
  rw [← tableBits_split, MachineTableSplit.timePolynomial_eval] at hs
  have hc := MachineCeilingPower.totalTime_le ExpanderFamily.growth n
  have hn := PortTables.vertices_le_tableBits_length t
  have hm := power_length_bound t
  have hsq := Nat.mul_le_mul_left (ExpanderFamily.growth + 8)
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2)
  have hmul := Nat.mul_le_mul_left (d + 8) hm
  simp only [otherPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  unfold otherTime cleanupTime
  unfold MachineCeilingPower.timeBound at hc
  nlinarith

end MinUncutGames.Foundations.Complexity.MachineVertexPadding

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineOverlayTable
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineOverlayTable

open _root_.Turing MachineComposition
open PCP PCP.GraphTables PCP.PreprocessingOverlayWords
open MachineCloudPadding


variable {A : Type} {d e : Nat}

def splitTapes (n m : Nat) (rows rawH : List Bool) : Tape → List Bool :=
  combine (MachineTableSplit.resultTapes n m rows) rawH

theorem initialTapes_memory (g h : List Bool) :
    initialTapes g h = memory g h [] [] [] [] [] [] [] [] := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [initialTapes, combine, extraTapes, MachineTableSplit.initialTapes,
      MachineTableSplit.tapes, memory]

theorem splitTapes_memory (n m : Nat) (rows rawH : List Bool) :
    splitTapes n m rows rawH = memory (encodeWords [n, m] ++ rows) rawH rows []
      (encodeWord n) (encodeWord m) [] [] [] [] := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [splitTapes, combine, extraTapes, MachineTableSplit.resultTapes,
      MachineTableSplit.tapes, memory]

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem encodeWords_flatten (items : List (List Nat)) :
    encodeWords items.flatten = (items.map encodeWords).flatten := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatten_cons, List.map_cons, encodeWords_append, ih]

theorem encodeWords_flatten_flatMap {α : Type*} (items : List (List α))
    (words : α → List Nat) :
    encodeWords (items.flatten.flatMap words) =
      (items.map fun xs => encodeWords (xs.flatMap words)).flatten := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      simp only [List.flatten_cons, List.flatMap_append, encodeWords_append, List.map_cons, ih]

def oldRows {n d : Nat} (G : PortTables.Table n d) (v : Fin n) := List.ofFn (row G v)
def expanderValues {n e : Nat} (H : ExpanderTables.Table n e) (v : Fin n) (p : Fin e) : Nat :=
  (ExpanderTables.reverseIndex H (ExpanderTables.rowIndex n e (v, p))).val

def oldBlock {n d : Nat} (G : PortTables.Table n d) (v : Fin n) : List Bool :=
  MachineLazyRows.recordsInput (oldRows G v)
def expanderBlock {n e : Nat} (H : ExpanderTables.Table n e) (v : Fin n) : List Bool :=
  encodeWords (List.ofFn (expanderValues H v))

def oldOutput {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) : List Bool :=
  MachineLazyRows.recordsOutput d (d + e) 0 (oldRows G v)
def expanderOutput {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) : List Bool :=
  MachineOverlayRows.streamOutput d e v.val (List.ofFn (expanderValues H v))
def outputBlock {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) : List Bool := oldOutput G e v ++ expanderOutput d H v

theorem oldOutput_eq {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) :
    oldOutput G e v = encodeWords ((List.ofFn (oldRow G e v)).flatMap rowWords) := by
  rw [encodeWords_flatMap]
  simp only [oldOutput, oldRows, MachineLazyRows.recordsOutput, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  change MachineLazyRows.reindexRowBits d (d + e) 0 (row G v p).tail.val
    (row G v p).reverseIndex.val (row G v p).relation = encodeWords (rowWords (oldRow G e v p))
  rw [oldRow_words]
  simp only [MachineLazyRows.reindexRowBits, MachinePortReindex.value, Nat.add_zero,
    oldReverseMap, row, PreprocessingLazyWords.row, List.cons_append, List.nil_append,
    encodeWords, List.append_assoc]

theorem expanderOutput_eq {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e) (v : Fin n) :
    expanderOutput d H v = encodeWords ((List.ofFn (expanderRow d H v)).flatMap rowWords) :=
  MachineOverlayRows.streamOutput_expanderRows d H v

theorem outputBlock_eq {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    outputBlock G H v = encodeWords ((vertexRows G H v).flatMap rowWords) := by
  rw [outputBlock, oldOutput_eq, expanderOutput_eq]
  simp only [vertexRows, List.flatMap_append, encodeWords_append]

theorem graphRows_blocks {n d : Nat} (G : PortTables.Table n d) :
    MachineTableSplit.rowsBits (PortTables.graphTable G) = (List.ofFn (oldBlock G)).flatten := by
  change encodeWords ((PortTables.flatRows G).toList.flatMap rowWords) = _
  rw [PreprocessingLazyWords.flatRows_list, encodeWords_flatten_flatMap, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (MachineLazyRows.recordsInput_eq_codec (oldRows G v)).symm

theorem expanderRows_blocks {n e : Nat} (H : ExpanderTables.Table n e) :
    encodeWords (ExpanderTableWords.rotationWords H) = (List.ofFn (expanderBlock H)).flatten := by
  rw [rotationWords_vertices, encodeWords_flatten, List.map_ofFn]
  rfl

theorem tableBits_blocks {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) :
    PortTables.tableBits (PreprocessingOverlayTables.overlay G H) =
      encodeWords [n, n * (d + e)] ++ (List.ofFn (outputBlock G H)).flatten := by
  rw [tableBits_overlay, encodeWords_append, encodeWords_flatten_flatMap, List.map_ofFn]
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  exact (outputBlock_eq G H v).symm

theorem oldFrame {n m : Nat} (g h gs hs nv mv f v out : List Bool)
    (rows : List (DartRow n m)) :
    MachineLazyRows.streamFrame oldTapes (memory g h gs hs nv mv f v [] []) rows out =
      memory g h (MachineLazyRows.recordsInput rows ++ gs) hs nv mv f v [] out := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [MachineLazyRows.streamFrame, oldTapes, memory, tail, oldReverse, relation,
      scratch, dividedCopy, quotient, newReverse, output, rowBuffer, graphStream]

theorem expanderFrame (g h gs hs nv mv f v t out : List Bool) (words : List Nat) :
    MachineOverlayRows.streamFrame expanderTapes (memory g h gs hs nv mv f v t []) words out =
      memory g h gs (encodeWords words ++ hs) nv mv f v t out := by
  funext k
  rcases k with i | i <;> fin_cases i <;>
    simp [MachineOverlayRows.streamFrame, expanderTapes, memory, tail, oldReverse,
      relation, scratch, dividedCopy, quotient, newReverse, output, rowBuffer, expanderStream]

def pairSteps {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (v : Fin n) (out : List Bool) : Nat :=
  MachineLazyRows.vertexSteps d (d + e) 0 (oldRows G v) out + (2 * (v.val + 1) + 1) +
    MachineOverlayRows.vertexSteps d e v.val (List.ofFn (expanderValues H v))
      (out ++ oldOutput G e v) + (v.val + 3)

def rawExpander {n e : Nat} (H : ExpanderTables.Table n e) : List Bool :=
  encodeWords (ExpanderTableWords.rotationWords H)

def outputPrefix {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (k : Nat) : List Bool := encodeWords [n, n * (d + e)] ++ emittedPrefix (outputBlock G H) k

theorem outputPrefix_step {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    outputPrefix G H (v.val + 1) = outputPrefix G H v.val ++ outputBlock G H v := by
  simp only [outputPrefix, prefix_step, List.append_assoc]

def loopBase {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Tape → List Bool :=
  memory (PortTables.tableBits G) (rawExpander H)
    (remaining (oldBlock G) (n - r)) (remaining (expanderBlock H) (n - r))
    (encodeWord n) (encodeWord (n * d)) [] (encodeWord (n - r)) [] (outputPrefix G H (n - r))

def loopCost {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e)
    (r : Nat) : Nat :=
  if hr : r < n then
    pairSteps G H ⟨n - (r + 1), by omega⟩ (outputPrefix G H (n - (r + 1)))
  else 0

def tableSteps {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) : Nat :=
  MachineTableSplit.exactSteps n (n * d) (MachineTableSplit.rowsBits (PortTables.graphTable G)) +
    preparationSteps n (rawExpander H) + MachineCountedLoop.totalSteps (loopCost G H) n +
    cleanupSteps n (n * d)

def expanderSize (d e n : Nat) : Nat := MachineOverlayRows.rowSizeBound d e n (n * e)
def blockSize (d e n : Nat) : Nat := d * oldSize d e n + e * expanderSize d e n

theorem oldOutput_length_le {n d : Nat} (G : PortTables.Table n d) (e : Nat) (v : Fin n) :
    (oldOutput G e v).length ≤ d * oldSize d e n := by
  have bound := flatMap_length_le (oldRows G v)
    (fun r => MachineLazyRows.reindexRowBits d (d + e) 0 r.tail.val r.reverseIndex.val r.relation)
    (oldSize d e n) (fun r _ => MachineLazyRows.reindexRowBits_length_le d (d + e) 0 r)
  simpa only [oldOutput, MachineLazyRows.recordsOutput, oldRows, List.length_ofFn] using bound

theorem expanderOutput_length_le {n e : Nat} (d : Nat) (H : ExpanderTables.Table n e)
    (v : Fin n) : (expanderOutput d H v).length ≤ e * expanderSize d e n := by
  have bound := flatMap_length_le (List.ofFn (expanderValues H v))
    (MachineOverlayRows.rowBits d e v.val) (expanderSize d e n) (by
      intro j hj
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hj
      have hrow := MachineOverlayRows.rowBits_length_le d e v.val (expanderValues H v p)
        (n * e) (MachineOverlayRows.expanderValues_bounded H v p)
      have hv := v.isLt.le
      unfold expanderSize MachineOverlayRows.rowSizeBound at *
      omega)
  simpa only [expanderOutput, MachineOverlayRows.streamOutput, List.length_ofFn] using bound

theorem outputBlock_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) :
    (outputBlock G H v).length ≤ blockSize d e n := by
  have hg := oldOutput_length_le G e v
  have hh := expanderOutput_length_le d H v
  simp only [outputBlock, List.length_append, blockSize]
  omega

def outputCapacity (d e n : Nat) : Nat := n + n * (d + e) + 2 + n * blockSize d e n

theorem outputPrefix_length_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (k : Nat) :
    (outputPrefix G H k).length ≤ outputCapacity d e n := by
  have hblocks := flatten_length_le ((List.ofFn (outputBlock G H)).take k)
    (blockSize d e n) (by
      intro xs hx
      have hm := List.mem_of_mem_take hx
      obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hm
      exact outputBlock_length_le G H v)
  have hlen : ((List.ofFn (outputBlock G H)).take k).length ≤ n := by
    simp only [List.length_take, List.length_ofFn]
    exact Nat.min_le_right _ _
  have hcap := Nat.mul_le_mul_right (blockSize d e n) hlen
  simp only [outputPrefix, emittedPrefix, List.length_append, encodeWords_length,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil, Nat.add_zero, outputCapacity]
  omega

def pairBudget (d e n : Nat) : Nat :=
  (d * (MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
    2 * (outputCapacity d e n + d * oldSize d e n) + 1) + 1) +
  (e * (MachineOverlayRows.rowCostBound d e n (n * e) +
    2 * (outputCapacity d e n + d * oldSize d e n + e * expanderSize d e n) + 1) + 1) +
  (3 * n + 6)

theorem pairSteps_le {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (out : List Bool)
    (hout : out.length ≤ outputCapacity d e n) : pairSteps G H v out ≤ pairBudget d e n := by
  have hold := MachineLazyRows.vertexSteps_le d (d + e) 0 (oldRows G v) out
  simp only [oldRows, List.length_ofFn] at hold
  have hgsize := oldOutput_length_le G e v
  have hnew := MachineOverlayRows.vertexSteps_le d e v.val (n * e)
    (List.ofFn (expanderValues H v)) (by
      intro j hj
      obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hj
      exact MachineOverlayRows.expanderValues_bounded H v p) (out ++ oldOutput G e v)
  simp only [List.length_ofFn, List.length_append] at hnew
  have hv := v.isLt.le
  have hsize : MachineOverlayRows.rowSizeBound d e v.val (n * e) ≤ expanderSize d e n := by
    unfold expanderSize MachineOverlayRows.rowSizeBound
    omega
  have hcost : MachineOverlayRows.rowCostBound d e v.val (n * e) ≤
      MachineOverlayRows.rowCostBound d e n (n * e) := by
    unfold MachineOverlayRows.rowCostBound
    change _ ≤ 8 * (n * e) + 4 * expanderSize d e n + _ + _ + 28
    omega
  have hsizeMul := Nat.mul_le_mul_left e hsize
  have holdBudget := Nat.mul_le_mul_left d
    (show MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
        2 * (out.length + d * MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)) + 1 ≤
      MachineLazyRows.rowCostBound (d + e) 0 n (n * d) +
        2 * (outputCapacity d e n + d * oldSize d e n) + 1 by
      unfold oldSize
      omega)
  have hnewBudget := Nat.mul_le_mul_left e
    (show MachineOverlayRows.rowCostBound d e v.val (n * e) +
        2 * (out.length + (oldOutput G e v).length + e * MachineOverlayRows.rowSizeBound d e v.val (n * e)) + 1 ≤
      MachineOverlayRows.rowCostBound d e n (n * e) +
        2 * (outputCapacity d e n + d * oldSize d e n + e * expanderSize d e n) + 1 by omega)
  unfold pairSteps pairBudget oldRows
  omega

theorem loopSteps_le {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    MachineCountedLoop.totalSteps (loopCost G H) n ≤ n * (pairBudget d e n + 1) + 1 := by
  apply MachineCountedLoop.totalSteps_le
  intro r hr
  rw [loopCost, dite_eq_left hr]
  exact pairSteps_le G H _ _ (outputPrefix_length_le G H _)

noncomputable def phasePolynomial (d e : Nat) : Polynomial Nat :=
  let x := Polynomial.X
  let C := Polynomial.C (R := Nat)
  let oldValue := C (d + e) * (x * C d) + x * C d + C 0
  let os := x + oldValue + C 8194
  let newValue := C (d + e) * (x * C e) + x * C e + C d
  let es := x + newValue + C MachineOverlayRows.trueBits.length + C 2
  let block := C d * os + C e * es
  let cap := x + x * C (d + e) + C 2 + x * block
  let oldCost := C 2 * x + C 8 * (x * C d) + oldValue + C 4 * os + C 8224
  let newCost := C 8 * (x * C e) + C 4 * es + newValue + C MachineOverlayRows.trueBits.length + C 28
  let pair := (C d * (oldCost + C 2 * (cap + C d * os) + C 1) + C 1) +
    (C e * (newCost + C 2 * (cap + C d * os + C e * es) + C 1) + C 1) +
    (C 3 * x + C 6)
  x * (pair + C 1) + C 1 + (C 2 * x + x * C d + C 8)

@[simp] theorem phasePolynomial_eval (d e n : Nat) :
    (phasePolynomial d e).eval n = n * (pairBudget d e n + 1) + 1 + cleanupSteps n (n * d) := by
  simp only [phasePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, pairBudget, outputCapacity, blockSize, oldSize, expanderSize,
    MachineLazyRows.rowSizeBound, MachineLazyRows.rowCostBound, MachineLazyRows.valueBound,
    MachineOverlayRows.rowSizeBound, MachineOverlayRows.rowCostBound,
    MachineOverlayRows.valueBound, cleanupSteps]

noncomputable def timePolynomial (d e : Nat) : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X + Polynomial.C 18 + phasePolynomial d e

theorem tableSteps_le {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    tableSteps G H ≤ (timePolynomial d e).eval ((PortTables.tableBits G).length + (rawExpander H).length) := by
  have hsplit := MachineTableSplit.exactSteps_le n (n * d)
    (MachineTableSplit.rowsBits (PortTables.graphTable G))
  have header : encodeWords [n, n * d] ++ MachineTableSplit.rowsBits (PortTables.graphTable G) =
      PortTables.tableBits G := (MachineTableSplit.tableBits_header_rows (PortTables.graphTable G)).symm
  rw [header, MachineTableSplit.timePolynomial_eval] at hsplit
  have hn := PortTables.vertices_le_tableBits_length G
  have hloop := loopSteps_le G H
  have hmono := natPolynomial_eval_mono (phasePolynomial d e)
    (show n ≤ (PortTables.tableBits G).length + (rawExpander H).length by omega)
  rw [phasePolynomial_eval] at hmono
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  unfold tableSteps preparationSteps
  omega

end MinUncutGames.Foundations.Complexity.MachineOverlayTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachinePaddedOverlay
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachinePaddedOverlay

open _root_.Turing MachineComposition MachineCloudPadding
open PCP


abbrev Tape := MachineVertexPadding.Tape ⊕ (MachineExpanderFamily.Tape ⊕ MachineOverlayTable.Tape)
abbrev Alphabet (_ : Tape) := Bool
abbrev Label (d : Nat) := MachineVertexPadding.Label d ⊕ (MachineExpanderFamily.Label baseDegree ⊕ MachineOverlayTable.Label d overlayDegree)

theorem overlayDegree_positive : 0 < overlayDegree :=
  Nat.mul_pos MachineExpanderFamily.baseDegree_positive MachineExpanderFamily.baseDegree_positive

def paddingTape (k : MachineVertexPadding.Tape) : Tape := .inl k

def paddingView : Tape → Option MachineVertexPadding.Tape
  | .inl k => some k
  | .inr _ => none

@[simp] theorem paddingView_left (k : MachineVertexPadding.Tape) : paddingView (paddingTape k) = some k := rfl

theorem paddingView_right (j : Tape) (k : MachineVertexPadding.Tape)
    (h : paddingView j = some k) : paddingTape k = j := by
  cases j with
  | inl j => cases Option.some.inj h; rfl
  | inr j => simp [paddingView] at h

def familyTape (k : MachineExpanderFamily.Tape) : Tape :=
  if k = .inr .remainingLevel then .inl .level else .inr (.inl k)

def familyView : Tape → Option MachineExpanderFamily.Tape
  | .inl .level => some (.inr .remainingLevel)
  | .inr (.inl k) => if k = .inr .remainingLevel then none else some k
  | _ => none

@[simp] theorem familyView_left (k : MachineExpanderFamily.Tape) : familyView (familyTape k) = some k := by
  by_cases h : k = .inr .remainingLevel
  · subst k; rfl
  · simp [familyTape, familyView, h]

theorem familyView_right (j : Tape) (k : MachineExpanderFamily.Tape)
    (h : familyView j = some k) : familyTape k = j := by
  rcases j with j | j
  · cases j <;> simp_all [familyView, familyTape]
  · rcases j with j | j
    · by_cases hj : j = .inr .remainingLevel <;> simp_all [familyView, familyTape]
    · simp [familyView] at h

def overlayTape (k : MachineOverlayTable.Tape) : Tape :=
  if k = MachineOverlayTable.graphArchive then .inl .output
  else if k = MachineOverlayTable.expanderArchive then .inr (.inl MachineExpanderFamily.tableTape)
  else .inr (.inr k)

def overlayView : Tape → Option MachineOverlayTable.Tape
  | .inl .output => some MachineOverlayTable.graphArchive
  | .inr (.inl k) => if k = MachineExpanderFamily.tableTape then some MachineOverlayTable.expanderArchive else none
  | .inr (.inr k) =>
      if k = MachineOverlayTable.graphArchive ∨ k = MachineOverlayTable.expanderArchive then none else some k
  | _ => none

@[simp] theorem overlayView_left (k : MachineOverlayTable.Tape) : overlayView (overlayTape k) = some k := by
  by_cases hg : k = MachineOverlayTable.graphArchive
  · subst k; rfl
  · by_cases he : k = MachineOverlayTable.expanderArchive
    · subst k; rfl
    · simp [overlayTape, overlayView, hg, he]

theorem overlayView_right (j : Tape) (k : MachineOverlayTable.Tape)
    (h : overlayView j = some k) : overlayTape k = j := by
  rcases j with j | j
  · cases j <;> simp_all [overlayView, overlayTape, MachineOverlayTable.graphArchive]
  · rcases j with j | j
    · by_cases hj : j = MachineExpanderFamily.tableTape
      · subst j
        have hk : MachineOverlayTable.expanderArchive = k := by
          simpa [overlayView] using h
        subst k
        rfl
      · simp [overlayView, hj] at h
    · by_cases hg : j = MachineOverlayTable.graphArchive
      · simp [overlayView, hg] at h
      · by_cases he : j = MachineOverlayTable.expanderArchive
        · simp [overlayView, he] at h
        · simp_all [overlayView, overlayTape]

variable {degree : Nat}

def paddingLabel (l : MachineVertexPadding.Label degree) : Label degree := .inl l
def familyLabel (l : MachineExpanderFamily.Label baseDegree) : Label degree := .inr (.inl l)
def overlayLabel (l : MachineOverlayTable.Label degree overlayDegree) : Label degree := .inr (.inr l)
def main : Label degree := paddingLabel (.splitCode .copyFirst)
def familyEntry : Label degree := familyLabel (.inr .initialize_)
def overlayEntry : Label degree := overlayLabel (.inl .copyFirst)

def memory (input padded level rotor count output : List Bool) : Tape → List Bool
  | .inl k => MachineVertexPadding.memory input padded [] [] [] level [] [] k
  | .inr (.inl (.inl (.inl .table))) => rotor
  | .inr (.inl (.inr .currentSize)) => count
  | .inr (.inl _) => []
  | .inr (.inr k) => if k = MachineOverlayTable.output then output else []

def padded {n d : Nat} (t : PortTables.Table n d) :=
  PreprocessingPaddingTables.pad t (PreprocessingLevels.le_paddedSize n)

def rotor (H : BaseTable) (n : Nat) : List Bool :=
  encodeWords (ExpanderTableWords.rotationWords
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n)))

def initialTapes {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) [] [] [] [] []

def paddedTapes {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord (PreprocessingLevels.boundedLevel n)) [] [] []

def familyTapes (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord 0) (rotor H n) (encodeWord (PreprocessingLevels.paddedSize n)) []

def finalTapes (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) : Tape → List Bool :=
  memory (PortTables.tableBits t) (PortTables.tableBits (padded t))
    (encodeWord 0) (rotor H n) (encodeWord (PreprocessingLevels.paddedSize n))
    (PortTables.tableBits (PreprocessingStageMaps.paddedOverlay H d ⟨n, t⟩).2)

def placeExecution {K Λ S : Type} [DecidableEq K]
    (tape : K → Tape) (view : Tape → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Label degree) (exit : Option (Label degree)) (extra : Tape → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ S)
    (target : Label degree → TM2.Stmt Alphabet (Label degree) S)
    (atLabels : ∀ l, target (labels l) = Placement.statement tape labels exit (source l))
    {a b : TM2.Cfg (fun _ : K => Bool) Λ S} {budget : Nat}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (Placement.configuration view labels exit extra a)
      (some (Placement.configuration view labels exit extra b)) budget :=
  liftExecutionInTime _ _ _
    (Placement.step_simulation tape view left right labels exit extra source target atLabels) run

theorem padding_initial_memory (input : List Bool) :
    Placement.tapes paddingView (MachineVertexPadding.memory input [] [] [] [] [] [] []) (fun _ => []) =
      memory input [] [] [] [] [] := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;> rfl
      · cases k <;> rfl
    · simp [Placement.tapes, paddingView, memory]

theorem padding_final_memory (input output level : List Bool) :
    Placement.tapes paddingView (MachineVertexPadding.memory input output [] [] [] level [] []) (fun _ => []) =
      memory input output level [] [] [] := by
  funext k
  rcases k with k | k
  · rfl
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;> rfl
      · cases k <;> rfl
    · simp [Placement.tapes, paddingView, memory]

theorem family_initial_memory (input output : List Bool) (level : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes (MachineExpanderFamily.initialTapes level []))
      (memory input output (encodeWord level) [] [] []) =
      memory input output (encodeWord level) [] [] [] := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, familyView, memory,
      MachineVertexPadding.memory, MachineExpanderFamily.toBoolTapes,
      MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
      MachineEmbedding.tapes]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
            MachineExpanderFamily.tableFrame, MachineEmbedding.tapes]
      · cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.initialTapes,
            MachineEmbedding.tapes]
    · rfl

theorem family_final_memory (H : BaseTable) (input output : List Bool) (level : Nat) :
    Placement.tapes familyView
      (MachineExpanderFamily.toBoolTapes (MachineExpanderFamily.familyTapes H level []))
      (memory input output (encodeWord level) [] [] []) =
      memory input output (encodeWord 0)
        (encodeWords (ExpanderTableWords.rotationWords (ExpanderTables.family H level)))
        (encodeWord (ExpanderTables.vertexCount overlayDegree level)) [] := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, familyView, memory,
      MachineVertexPadding.memory, MachineExpanderFamily.toBoolTapes,
      MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
      MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
      MachineEmbedding.tapes]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
            MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.tableFrame,
            MachineEmbedding.tapes]
      · cases k <;>
          simp [Placement.tapes, familyView, memory, MachineExpanderFamily.toBoolTapes,
            MachineExpanderFamily.toBoolWord, MachineExpanderFamily.familyTapes,
            MachineExpanderFamily.boundaryTapes, MachineExpanderFamily.extraFrame,
            MachineEmbedding.tapes, overlayDegree, PreprocessingRegularTables.internalDegree,
            ExpanderRowControl.degree]
    · simp [Placement.tapes, familyView, memory]

theorem rotationWords_resize {n m q : Nat} (h : n = m) (H : ExpanderTables.Table n q) :
    ExpanderTableWords.rotationWords (PreprocessingRegularTables.resizeTable h H) =
      ExpanderTableWords.rotationWords H := by
  cases h
  rfl

theorem rotor_familyAt (H : BaseTable) (n : Nat) :
    MachineOverlayTable.rawExpander (PreprocessingStageMaps.familyAt H n) = rotor H n := by
  unfold MachineOverlayTable.rawExpander PreprocessingStageMaps.familyAt rotor
  exact congrArg encodeWords (rotationWords_resize
    (PreprocessingLevels.table_vertexCount_eq_paddedSize n)
    (ExpanderTables.family H (PreprocessingLevels.boundedLevel n)))

theorem overlay_memory (input graph raw count output : List Bool) :
    Placement.tapes overlayView
      (MachineOverlayTable.memory graph raw [] [] [] [] [] [] [] output)
      (memory input graph (encodeWord 0) raw count []) =
      memory input graph (encodeWord 0) raw count output := by
  funext k
  rcases k with k | k
  · cases k <;> simp [Placement.tapes, overlayView, memory, MachineVertexPadding.memory,
      MachineOverlayTable.memory, MachineOverlayTable.graphArchive]
  · rcases k with k | k
    · rcases k with k | k
      · rcases k with k | k <;> cases k <;>
          simp [Placement.tapes, overlayView, memory, MachineExpanderFamily.tableTape,
            MachineOverlayTable.memory, MachineOverlayTable.expanderArchive]
      · cases k <;>
          simp [Placement.tapes, overlayView, memory, MachineExpanderFamily.tableTape]
    · rcases k with k | k <;> fin_cases k <;>
        simp [Placement.tapes, overlayView, memory, MachineOverlayTable.memory,
          MachineOverlayTable.graphArchive, MachineOverlayTable.expanderArchive,
          MachineOverlayTable.output]

theorem archive_length_le (H : BaseTable) {n d : Nat} (t : PortTables.Table n d) :
    (PortTables.tableBits (padded t)).length + (rotor H n).length ≤
      (archivePolynomial d).eval (PortTables.tableBits t).length := by
  let m := PreprocessingLevels.paddedSize n
  let s := ExpanderFamily.growth * ((PortTables.tableBits t).length + 1)
  have hm : m ≤ s := MachineVertexPadding.power_length_bound t
  have hmd : m*d ≤ s*d := Nat.mul_le_mul_right d hm
  have hmq : m*overlayDegree ≤ s*overlayDegree := Nat.mul_le_mul_right overlayDegree hm
  have hg := GraphTables.tableBits_length_le (PortTables.graphTable (padded t))
  change (PortTables.tableBits (padded t)).length ≤
    m + m*d + 2 + m*d*(m + m*d + 8192) at hg
  have hg' := hg.trans (Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add hm hmd) 2)
    (Nat.mul_le_mul hmd (Nat.add_le_add_right (Nat.add_le_add hm hmd) 8192)))
  have hr := ExpanderTableWords.encode_rotationWords_length_le
    (PreprocessingStageMaps.familyAt H n)
  change (MachineOverlayTable.rawExpander (PreprocessingStageMaps.familyAt H n)).length ≤
    (m*overlayDegree)*(m*overlayDegree+1) at hr
  rw [rotor_familyAt] at hr
  have hr' := hr.trans (Nat.mul_le_mul hmq (Nat.add_le_add_right hmq 1))
  have h := Nat.add_le_add hg' hr'
  simpa only [archivePolynomial, sizePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat,
    s] using h

end MinUncutGames.Foundations.Complexity.MachinePaddedOverlay

end
section
namespace MinUncutGames.Foundations.Complexity.MachinePaddedOverlayRuntime

open _root_.Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label )


noncomputable def cleanupTapes : List Tape :=
  (Finset.univ.erase (.inr (.inr MachineOverlayTable.output) : Tape)).toList

end MinUncutGames.Foundations.Complexity.MachinePaddedOverlayRuntime

end
section
namespace MinUncutGames.Foundations.Complexity.MachineLazyCodec
open PCP.GraphTables PCP.PreprocessingLazyWords

theorem encodeWords_flatMap {α : Type*} (items : List α) (words : α → List Nat) :
    encodeWords (items.flatMap words) = items.flatMap (fun x => encodeWords (words x)) := by
  induction items with
  | nil => rfl
  | cons item items ih => simp only [List.flatMap_cons, encodeWords_append, ih]

end MinUncutGames.Foundations.Complexity.MachineLazyCodec

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLazyTable
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineLazyTable

open _root_.Turing MachineComposition PCP
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)


def loopTapes (d : Nat) (input : List Bool) (n m left v : Nat)
    (source output : List Bool) : Tape → List Bool :=
  frame input source output (encodeWord n) (encodeWord m) (encodeWord left)
    (encodeWord v) (encodeWord (2 * d * v))

def prefixSteps (n m : Nat) (rows : List Bool) : Nat :=
  2 * (encodeWords [n, m] ++ rows).length + 5 * n + 3 * m + 17

def inputBlocks {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) : List Bool :=
  events.flatMap (fun v => MachineLazyRows.recordsInput (List.ofFn (PreprocessingLazyWords.row table v)))

theorem encodeWords_flatMap {α : Type} (xs : List α) (f : α → List Nat) :
    encodeWords (xs.flatMap f) = xs.flatMap (fun x => encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, encodeWords_append, ih]

theorem inputBlocks_codec {n d : Nat} (table : PortTables.Table n d) (events : List (Fin n)) :
    inputBlocks table events = encodeWords
      ((events.flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatMap
        GraphTables.rowWords) := by
  rw [List.flatMap_assoc, encodeWords_flatMap]
  simp only [inputBlocks, MachineLazyRows.recordsInput_eq_codec]

theorem input_table_codec {n d : Nat} (table : PortTables.Table n d) :
    PortTables.tableBits table = encodeWords [n, n * d] ++ inputBlocks table (List.finRange n) := by
  rw [inputBlocks_codec]
  change encodeWords (PortTables.tableWords table) = _
  rw [PortTables.tableWords_eq, PreprocessingLazyWords.flatRows_list, encodeWords_append]
  have hrows : (List.ofFn (fun v => List.ofFn (PreprocessingLazyWords.row table v))).flatten =
      (List.finRange n).flatMap (fun v => List.ofFn (PreprocessingLazyWords.row table v)) := by
    rw [List.ofFn_eq_map]
    rfl
  rw [hrows]

theorem output_length_le {n d : Nat} (table : PortTables.Table n d) :
    (PortTables.tableBits (PreprocessingOverlayTables.lazy table)).length ≤
      20000 * ((PortTables.tableBits table).length + 1) ^ 2 := by
  let L := (PortTables.tableBits table).length
  have hn : n ≤ L := PortTables.vertices_le_tableBits_length table
  have hm : n * d ≤ L := GraphTables.darts_le_tableBits_length (PortTables.graphTable table)
  have h := GraphTables.tableBits_length_le
    (PortTables.graphTable (PreprocessingOverlayTables.lazy table))
  change (PortTables.tableBits (PreprocessingOverlayTables.lazy table)).length ≤
    n + n * (2 * d) + 2 + n * (2 * d) * (n + n * (2 * d) + 8192) at h
  have hdouble : n * (2 * d) = 2 * (n * d) := by ac_rfl
  rw [hdouble] at h
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm)
    (Nat.add_le_add_right (Nat.add_le_add hn (Nat.mul_le_mul_left 2 hm)) 8192)
  change _ ≤ 20000 * (L + 1) ^ 2
  nlinarith only [h, hn, hm, hmul]

end MinUncutGames.Foundations.Complexity.MachineLazyTable

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineLazyTableRuntime
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.PreprocessingFinishRuntime

open _root_.Turing MinUncutGames.Foundations.Complexity
open PreprocessingRegularTables

def finish (H : PreprocessingTables.BaseTable) (d : Nat) (input : PortTables.Input d) :
    PortTables.Input (2 * (d + internalDegree)) :=
  PreprocessingStageMaps.lazy (d + internalDegree)
    (PreprocessingStageMaps.paddedOverlay H d input)

end MinUncutGames.Foundations.PCP.PreprocessingFinishRuntime

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_PoweringMachineRuntime
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PoweringMachineRuntime

open _root_.Turing MachineComposition PCP PoweringMachineGlobal


variable {vertices d : Nat}

def beforeFinishBudget (graph : PortTables.Table vertices d) (n : Nat) : Nat :=
  (3 * vertices + 5) + (vertices *
    (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1)

end MinUncutGames.Foundations.Complexity.PoweringMachineRuntime

end

end OAI
end


