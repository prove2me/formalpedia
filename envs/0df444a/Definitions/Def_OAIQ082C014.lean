-- Prove2me | Definitions.Def_OAIQ082C014
-- name    : OAIQ082C014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:37:27.950217+00:00
-- url     : https://prove2.me/theorems/fdba8e3b-a1af-41c5-8df3-9adc7eab2d59
-- title:
--   Definitions bundle OAIQ082C014 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 403 declarations of OpenAI's Lean: 179 definitions, 5 inductive types or structures, 4 instances and 215 theorems. The definitions and types are `OAI.BinPackingGap.ExtensionVerifierMachine.Fields.encodedWords`, `OAI.BinPackingGap.ExtensionVerifierMachine.Fields.extensionInTime`, `OAI.BinPackingGap.ExtensionVerifierMachine.Fields.nextRestore`, `OAI.BinPackingGap.ExtensionVerifierMachine.Fields.outputTape`, `OAI.BinPackingGap.ExtensionVerifierMachine.Fields.restoreLabel`, `OAI.BinPackingGap.ExtensionVerifierMachine.Fields.savedTape`, `OAI.BinPackingGap.FiniteTapeProgram.Code.outputsInTime`, `OAI.BinPackingGap.GraphFieldMachine.Label`, `OAI.BinPackingGap.GraphFieldMachine.State`, `OAI.BinPackingGap.GraphFieldMachine.clean`, `OAI.BinPackingGap.GraphFieldMachine.emit`, `OAI.BinPackingGap.GraphFieldMachine.fieldBits`, `OAI.BinPackingGap.GraphFieldMachine.fieldsOutput`, `OAI.BinPackingGap.GraphFieldMachine.instruction`, `OAI.BinPackingGap.GraphFieldMachine.resultTapes`, `OAI.BinPackingGap.GraphFieldMachine.scanOutput`, `OAI.BinPackingGap.GraphFieldMachine.steps`, `OAI.BinPackingGap.GraphPackingJobStream.endpointPower`, `OAI.BinPackingGap.GraphPackingJobs.clearedOther`, `OAI.BinPackingGap.GraphPackingJobs.completedInputs`, `OAI.BinPackingGap.GraphPackingJobs.inputs`, `OAI.BinPackingGap.GraphPackingJobs.inventory`, `OAI.BinPackingGap.GraphPackingJobs.loadEndpoint`, `OAI.BinPackingGap.GraphPackingJobs.loadedOther`, `OAI.BinPackingGap.GraphPackingPreparation.baseTapes`, `OAI.BinPackingGap.GraphPackingPreparation.binBound`, `OAI.BinPackingGap.GraphPackingPreparation.geometryFactor`, `OAI.BinPackingGap.GraphPackingPreparation.initialTapes`, `OAI.BinPackingGap.GraphPackingPreparation.parsedOther`, `OAI.BinPackingGap.GraphPackingPreparation.parsedTapes`, `OAI.BinPackingGap.GraphPackingPreparation.preparedInputs`, `OAI.BinPackingGap.GraphPackingPreparation.preparedOther`, `OAI.BinPackingGap.GraphPackingPreparation.preparedTapes`, `OAI.BinPackingGap.GraphPackingPreparation.preparedWork`, `OAI.BinPackingGap.GraphPackingPreparation.repetitions`, `OAI.BinPackingGap.GraphPackingPreparation.setupOther`, `OAI.BinPackingGap.GraphPackingRegisters.Numerator`, `OAI.BinPackingGap.GraphPackingRegisters.Other`, `OAI.BinPackingGap.GraphPackingRegisters.Register`, `OAI.BinPackingGap.GraphPackingRegisters.Tape` and 144 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_BinaryToTallyMachine`, `BinPacking_Arithmetic_GraphPackingRegisters`, `BinPacking_Arithmetic_GraphTallyMachine`, `BinPacking_Arithmetic_PackingRegisterFrame`, `BinPacking_Arithmetic_PackingRegisterUpdate`, `BinPacking_Inventory_IntegralSpeciesCounts`, `BinPacking_Inventory_InventoryCoverage`, `BinPacking_Inventory_InventoryScores`, `BinPacking_Inventory_LocalCompletionCoverage`, `BinPacking_Inventory_PackingConstantPool`, `BinPacking_Inventory_PackingInventoryDescriptors`, `BinPacking_Machines_GraphPackingJobList`, `BinPacking_Machines_GraphPackingOutput`, `BinPacking_Machines_GraphPackingPreparationFinish`, `BinPacking_Machines_GraphPackingStockStreams`, `BinPacking_Machines_IntegerPackingArithmetic`, `BinPacking_Machines_PackingCountedProgram`, `BinPacking_Machines_PackingJobLoop`, `BinPacking_Machines_PackingPowerProgram`, `BinPacking_Machines_PackingSetupGraph`, `BinPacking_Machines_PackingVertexUpdate`, `BinPacking_Packing_ExtractedCover`, `BinPacking_Packing_LocalTemplateBases`, `BinPacking_Packing_PackingCoordinates`, `BinPacking_Packing_PackingScalarExpression`, `BinPacking_Packing_PhaseIteration`, `BinPacking_Search_ExtensionValidationMachine`, `BinPacking_Search_ExtensionVerifierMachine`, `BinPacking_Trees_CompetingTrees`, `BinPacking_Trees_IntegerTreeGeometry`, `BinPacking_Trees_TestGeometry`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C000`, `OAIQ082C001`, `OAIQ082C006`, `OAIQ082C007`, `OAIQ082C008` and `OAIQ082C009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C020`, `OAIQ082C021` and `OAIQ082C022`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C000
import Definitions.Def_OAIQ082C001
import Definitions.Def_OAIQ082C006
import Definitions.Def_OAIQ082C007
import Definitions.Def_OAIQ082C008
import Definitions.Def_OAIQ082C009

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_PackingRegisterFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingRegisterFrame

open BinaryRegisterProgram

variable {Local Global K : Type}

theorem registerTapes_eq_self (slot : (Local ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (values : Local → Nat)
    (shape : ∀ i, base (slot i) = registerWords values i) :
    registerTapes slot base values = base := by
  funext k
  by_cases hk : ∃ i, slot i = k
  · obtain ⟨i, rfl⟩ := hk
    rw [registerTapes_slot, shape]
  · exact registerTapes_other slot base values k hk

theorem restrict (slot : (Global ⊕ Fin 6) ↪ K) (register : Local ↪ Global)
    (base : K → List Bool) (values : Global → Nat) :
    registerTapes (localSlots slot register) (registerTapes slot base values)
      (values ∘ register) = registerTapes slot base values := by
  apply registerTapes_eq_self
  intro i
  cases i <;> simp [Function.comp_def]

theorem replace (slot : (Global ⊕ Fin 6) ↪ K) (register : Local ↪ Global)
    (base : K → List Bool) (before after : Global → Nat) (localAfter : Local → Nat)
    (inside : ∀ r, after (register r) = localAfter r)
    (outside : ∀ r, (¬ ∃ l, register l = r) → after r = before r) :
    registerTapes (localSlots slot register) (registerTapes slot base before) localAfter =
      registerTapes slot base after := by
  funext k
  by_cases hk : ∃ i, slot i = k
  · obtain ⟨i, rfl⟩ := hk
    cases i with
    | inl r =>
        by_cases hr : ∃ l, register l = r
        · obtain ⟨l, rfl⟩ := hr
          change registerTapes (localSlots slot register) _ localAfter
            (localSlots slot register (.inl l)) = _
          simp only [registerTapes_reg, inside]
        · have hlocal : ¬ ∃ i, localSlots slot register i = slot (.inl r) := by
            rintro ⟨i, hi⟩
            have h := slot.injective hi
            cases i with
            | inl l => exact hr ⟨l, Sum.inl.inj h⟩
            | inr j => cases h
          rw [registerTapes_other _ _ _ _ hlocal, registerTapes_reg,
            registerTapes_reg, outside r hr]
    | inr j =>
        change registerTapes (localSlots slot register) _ localAfter
          (localSlots slot register (.inr j)) = _
        simp only [registerTapes_scratch]
  · have hlocal : ¬ ∃ i, localSlots slot register i = k := by
      rintro ⟨i, hi⟩
      exact hk ⟨withScratch register i, hi⟩
    rw [registerTapes_other _ _ _ _ hlocal, registerTapes_other _ _ _ _ hk,
      registerTapes_other _ _ _ _ hk]

theorem external_update [DecidableEq K] (slot : (Global ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (values : Global → Nat) (output : K) (outside : ∀ i, slot i ≠ output)
    (word : List Bool) :
    registerTapes slot (Function.update base output word) values =
      Function.update (registerTapes slot base values) output word := by
  funext k
  by_cases hk : k = output
  · subst k
    have hn : ¬ ∃ i, slot i = output := by rintro ⟨i, hi⟩; exact outside i hi
    simp [registerTapes_other _ _ _ _ hn]
  · by_cases hs : ∃ i, slot i = k
    · obtain ⟨i, rfl⟩ := hs
      simp [outside i]
    · simp [registerTapes_other _ _ _ _ hs, hk]

end BinPackingGap.PackingRegisterFrame

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_GraphTallyMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.instFintypeGlobalSpecies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

namespace GraphFields

open BinaryEncoding

theorem vertices_length_le_bits (fields : GraphFields) :
    fields.vertices.length ≤ fields.bits.length := by
  have h := list_length_le_bits_length natBits fields.vertices
  rw [bits_length]
  omega

theorem endpoints_length_le_bits (fields : GraphFields) :
    fields.endpoints.length ≤ fields.bits.length := by
  have h := list_length_le_bits_length (pairBits natBits natBits) fields.endpoints
  rw [bits_length]
  omega

end GraphFields

namespace GraphReductionInput

def fields (input : GraphReductionInput) : GraphFields :=
  ⟨input.k, List.range input.graph.n, input.graph.endpointPairs⟩

@[simp] theorem fields_k (input : GraphReductionInput) : input.fields.k = input.k := rfl

@[simp] theorem fields_vertices (input : GraphReductionInput) :
    input.fields.vertices = List.range input.graph.n := rfl

@[simp] theorem fields_endpoints (input : GraphReductionInput) :
    input.fields.endpoints = input.graph.endpointPairs := rfl

end GraphReductionInput

def graphBits (input : GraphReductionInput) : List Bool := input.fields.bits

theorem graph_vertexCount_le_bits (input : GraphReductionInput) :
    input.graph.n ≤ (graphBits input).length := by
  simpa [graphBits, GraphReductionInput.fields] using
    GraphFields.vertices_length_le_bits input.fields

theorem graph_edgeCount_le_bits (input : GraphReductionInput) :
    input.graph.edges.length ≤ (graphBits input).length := by
  simpa [graphBits, GraphReductionInput.fields] using
    GraphFields.endpoints_length_le_bits input.fields

end BinPackingGap

namespace BinPackingGap.GraphTallyMachine

open Turing
open BinPackingGap.BinaryEncoding
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction

instance instFintypeSlot : Fintype Slot where
  elems := {.header, .vertex, .edgeFirst, .edgeSecond}
  complete slot := by cases slot <;> simp

inductive Mode
  | vertices
  | endpoints
  | name (slot : Slot)
  | digit (slot : Slot)
  | done
  deriving DecidableEq, Fintype

def afterName : Slot → Mode
  | .header => .vertices
  | .vertex => .vertices
  | .edgeFirst => .name .edgeSecond
  | .edgeSecond => .endpoints

def initial : Mode := .name .header

def transition : Mode → Bool → Mode
  | .vertices, true => .name .vertex
  | .vertices, false => .endpoints
  | .endpoints, true => .name .edgeFirst
  | .endpoints, false => .done
  | .name slot, true => .digit slot
  | .name slot, false => afterName slot
  | .digit slot, _ => .name slot
  | .done, _ => .done

end BinPackingGap.GraphTallyMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingPowerProgram
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.FiniteTapeProgram

section

open Turing BinPackingGames.Foundations.Complexity MachineComposition

variable (K S : Type)

variable {K S}

variable [DecidableEq K]

theorem Exec.trace {c : Code (K := K) (S := S)} {d e : Data K S} {n : Nat}
    (h : Exec c d n e) {Λ : Type} (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ S)
    (labels : c.Label → Λ) (exit : Option Λ)
    (atLabels : ∀ l, program (labels l) = c.instruction labels exit l) :
    (advance (TM2.step program))^[n]
      (some ⟨some (labels c.entry), d.state, d.tapes⟩) =
    some ⟨exit, e.state, e.tapes⟩ := by
  induction h generalizing Λ with
  | atom a d =>
      change some (TM2.stepAux (program (labels ())) d.state d.tapes) = _
      rw [atLabels, Code.instruction, Action.stepAux_statement, stepAux_jump]
  | routine finite main source d e n run =>
      exact MachineSubroutine.trace labels exit source program atLabels n _ _ run
  | @seq a b d e f n m ha hb iha ihb =>
      have first := iha program (fun l => labels (.inl l))
        (some (labels (.inr b.entry))) (fun l => atLabels (.inl l))
      have second := ihb program (fun l => labels (.inr l)) exit
        (fun l => atLabels (.inr l))
      rw [Nat.add_comm n m, Function.iterate_add_apply]
      change (advance (TM2.step program))^[m]
        ((advance (TM2.step program))^[n]
          (some ⟨some (labels (.inl a.entry)), d.state, d.tapes⟩)) = _
      rw [first]
      exact second
  | @branch_true p a b d e n hp h ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[n]
        (some (TM2.stepAux (program (labels (.inl ()))) d.state d.tapes)) = _
      rw [atLabels]
      simp only [Code.instruction, TM2.stepAux, hp, Bool.cond_true, jump]
      exact ih program (fun l => labels (.inr (.inl l))) exit
        (fun l => atLabels (.inr (.inl l)))
  | @branch_false p a b d e n hp h ih =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[n]
        (some (TM2.stepAux (program (labels (.inl ()))) d.state d.tapes)) = _
      rw [atLabels]
      simp only [Code.instruction, TM2.stepAux, hp, Bool.cond_false, jump]
      exact ih program (fun l => labels (.inr (.inr l))) exit
        (fun l => atLabels (.inr (.inr l)))
  | @loop_false g p a d hp =>
      change some (TM2.stepAux (program (labels (.inl ()))) d.state d.tapes) = _
      rw [atLabels, Code.instruction, Action.stepAux_statement]
      simp only [TM2.stepAux, hp, Bool.cond_false, stepAux_jump]
  | @loop_true g p a d e f n m hp hb hl ihb ihl =>
      rw [Function.iterate_succ_apply]
      change (advance (TM2.step program))^[n + m]
        (some (TM2.stepAux (program (labels (.inl ()))) d.state d.tapes)) = _
      rw [atLabels, Code.instruction, Action.stepAux_statement]
      simp only [TM2.stepAux, hp, Bool.cond_true, jump]
      have body := ihb program (fun l => labels (.inr l))
        (some (labels (.inl ()))) (fun l => atLabels (.inr l))
      rw [Nat.add_comm n m, Function.iterate_add_apply, body]
      exact ihl program labels exit atLabels

variable [Fintype K] [Fintype S]

def Code.outputsInTime (c : Code (K := K) (S := S)) (input output : K) (initial : S)
    (word result : List Bool) (n budget : Nat)
    (run : Exec c ⟨initial, Function.update (fun _ => []) input word⟩ n
      ⟨initial, Function.update (fun _ => []) output result⟩)
    (bound : n ≤ budget) :
    TM2OutputsInTime (c.machine input output initial) word (some result) budget where
  steps := n
  evals_in_steps := by
    have initialEq : initList (c.machine input output initial) word =
        (⟨some c.entry, initial, Function.update (fun _ => []) input word⟩ :
          (c.machine input output initial).Cfg) := by
      unfold initList
      dsimp only [Code.machine]
      congr 1
      funext k
      by_cases h : k = input
      · subst k; simp [Function.update]; rfl
      · simp [Function.update, h]
    have finalEq : haltList (c.machine input output initial) result =
        (⟨none, initial, Function.update (fun _ => []) output result⟩ :
          (c.machine input output initial).Cfg) := by
      unfold haltList
      dsimp only [Code.machine]
      congr 1
      funext k
      by_cases h : k = output
      · subst k; simp [Function.update]; rfl
      · simp [Function.update, h]
    change (advance (TM2.step (c.instruction id none)))^[n]
      (some (initList (c.machine input output initial) word)) =
        some (haltList (c.machine input output initial) result)
    rw [initialEq, finalEq]
    exact run.trace (c.instruction id none) id none (fun _ => rfl)
  steps_le_m := bound

end

open Turing BinPackingGames.Foundations.Complexity MachineComposition

variable {K S : Type} [DecidableEq K] [Fintype K] [Fintype S]

theorem Exec.stack_length_le {c : Code (K := K) (S := S)}
    {d e : Data K S} {n : Nat} (run : Exec c d n e)
    (input output : K) (initial : S) (k : K) :
    (e.tapes k).length ≤ (d.tapes k).length +
      n * Runtime.programPushBound (c.machine input output initial) := by
  let tm := c.machine input output initial
  have execution : StateTransition.EvalsToInTime tm.step
      (⟨some c.entry, d.state, d.tapes⟩ : tm.Cfg)
      (some ⟨none, e.state, e.tapes⟩) n := {
    steps := n
    evals_in_steps := by
      change (advance (TM2.step (c.instruction id none)))^[n]
        (some ⟨some c.entry, d.state, d.tapes⟩) =
        some ⟨none, e.state, e.tapes⟩
      exact run.trace (c.instruction id none) id none (fun _ => rfl)
    steps_le_m := le_rfl
  }
  exact Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) execution

end BinPackingGap.FiniteTapeProgram

namespace BinPackingGap.LiteralSlotGraphMachine

open Turing BinPackingGames.Foundations BinPackingGames.Foundations.Target
open FiniteTapeProgram

abbrev NonemptyFormula := {F : Formula // F.clauses ≠ []}

end BinPackingGap.LiteralSlotGraphMachine

namespace BinPackingGap.PackingFieldDecodeMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open FiniteTapeProgram

variable {K A : Type} [DecidableEq K]

def code (slots : Fin 3 ↪ K) : Code (K := K) (S := State A) :=
  .routine ExtensionNatMachine.Label inferInstance .scan
    (ExtensionNatMachine.statement (decoderSlots slots) id none none)

theorem decodeNat_steps (n : Nat) :
    2 * n.size + 2 = (BinaryEncoding.natBits n).length + 1 := by
  simp [Nat.add_assoc]

end BinPackingGap.PackingFieldDecodeMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_BinaryToTallyMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.RegisterFrameEmission

open Turing BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram
open BinPackingGames.Reduction.MachineTransfer

variable {Reg K A : Type} [DecidableEq Reg] [DecidableEq K]

omit [DecidableEq Reg] in
theorem external_update (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (values : Reg → Nat) (output : K) (outside : ∀ i, slot i ≠ output) (word : List Bool) :
    registerTapes slot (Function.update base output word) values =
      Function.update (registerTapes slot base values) output word := by
  classical
  funext k
  by_cases hk : k = output
  · subst k
    have ho : ¬ ∃ i, slot i = output := by rintro ⟨i, hi⟩; exact outside i hi
    simp [registerTapes_other slot _ values output ho]
  · by_cases hs : ∃ i, slot i = k
    · obtain ⟨i, rfl⟩ := hs
      simp [outside i]
    · simp only [registerTapes_other slot _ values k hs, Function.update_of_ne hk]

theorem exec (slot : (Reg ⊕ Fin 6) ↪ K) (base : K → List Bool) (values : Reg → Nat)
    (r : Reg) (output : K) (outside : ∀ i, slot i ≠ output) (ambient : A) :
    Exec (code (slot (.inl r)) output)
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩
      ((values r).size + 1)
      ⟨BinaryAddMachine.clean ambient,
        registerTapes slot (Function.update base output
          ((BinaryEncoding.natBits (values r)).reverse ++ base output))
          (Function.update values r 0)⟩ := by
  classical
  let current := registerTapes slot base values
  have hout : current output = base output := by
    apply registerTapes_other
    rintro ⟨i, hi⟩
    exact outside i hi
  have hsrc : current (slot (.inl r)) = (values r).bits := registerTapes_reg _ _ _ _
  have initial_eq : tapesAt (slot (.inl r)) output current (values r).bits (base output) = current := by
    rw [← hsrc, ← hout]
    exact tapesAt_self _ _ _
  have clear_eq : Function.update current (slot (.inl r)) [] =
      registerTapes slot base (Function.update values r 0) := by
    simpa only [current, Nat.zero_bits] using registerTapes_update slot base values r 0
  have final_eq : tapesAt (slot (.inl r)) output current []
      ((BinaryEncoding.natBits (values r)).reverse ++ base output) =
      registerTapes slot (Function.update base output
        ((BinaryEncoding.natBits (values r)).reverse ++ base output))
        (Function.update values r 0) := by
    rw [tapesAt, clear_eq, external_update slot base _ output outside]
  refine Exec.routine inferInstance ()
    (fun _ => FrameEmitMachine.instruction (slot (.inl r)) output () none)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot base values⟩
    ⟨BinaryAddMachine.clean ambient,
      registerTapes slot (Function.update base output
        ((BinaryEncoding.natBits (values r)).reverse ++ base output))
        (Function.update values r 0)⟩ ((values r).size + 1) ?_
  have run := FrameEmitMachine.trace (A := (A × Bool) × Option Bool) (slot (.inl r)) output (outside (.inl r)) () none
    (fun _ : Unit => FrameEmitMachine.instruction (slot (.inl r)) output () none)
    rfl current ((ambient, false), none) (values r).bits (base output)
  change (BinPackingGames.Foundations.Complexity.MachineComposition.advance
    (Turing.TM2.step (fun _ : Unit =>
      FrameEmitMachine.instruction (slot (.inl r)) output () none)))^[(values r).bits.length + 1]
    (some (⟨some (), BinaryAddMachine.clean ambient,
      tapesAt (slot (.inl r)) output current (values r).bits (base output)⟩ :
        Turing.TM2.Cfg (fun _ : K => Bool) Unit (BinaryAddMachine.State A))) =
    some ⟨none, BinaryAddMachine.clean ambient,
      tapesAt (slot (.inl r)) output current []
        ((BinaryEncoding.natBits (values r)).reverse ++ base output)⟩ at run
  rw [Nat.size_eq_bits_len, initial_eq, final_eq] at run
  exact run

end BinPackingGap.RegisterFrameEmission

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_IntegerPackingArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.IntegerPackingArithmetic

theorem itemNumerator_ratio {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ) :
    (itemNumerator geom subclass label W : ℚ) / (sizeDenominator n geom : ℚ) =
      encodedSize subclass label ((W : ℚ) / geom) := by
  exact signedNumerator_ratio n geom hgeom (primaryScore subclass) (secondaryScore subclass label) W

theorem itemNumerator_pos_lt {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    0 < itemNumerator geom subclass label W ∧
      itemNumerator geom subclass label W < (sizeDenominator n geom : ℤ) := by
  have hd : (0 : ℚ) < sizeDenominator n geom := by
    exact_mod_cast sizeDenominator_pos n geom hgeom
  have hs := encodedSize_mem_interval subclass label ((W : ℚ) / geom) hW
  rw [← itemNumerator_ratio geom hgeom subclass label W] at hs
  have hpos : (0 : ℚ) < (itemNumerator geom subclass label W : ℚ) := by
    have hdiv : (0 : ℚ) < (itemNumerator geom subclass label W : ℚ) /
        (sizeDenominator n geom : ℚ) := lt_trans (by norm_num) hs.1
    rcases div_pos_iff.mp hdiv with h | h
    · exact h.1
    · exact (not_lt_of_ge hd.le h.2).elim
  have hlt : (itemNumerator geom subclass label W : ℚ) < (sizeDenominator n geom : ℚ) := by
    have h := (div_lt_iff₀ hd).mp hs.2
    simpa only [one_mul] using h
  constructor
  · exact_mod_cast hpos
  · exact_mod_cast hlt

theorem rawItem_numerator_cast {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    ((rawItem geom subclass label W).1 : ℤ) = itemNumerator geom subclass label W := by
  exact Int.toNat_of_nonneg (itemNumerator_pos_lt geom hgeom subclass label W hW).1.le

theorem rawItem_valid {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    0 < (rawItem geom subclass label W).1 ∧
      (rawItem geom subclass label W).1 < (rawItem geom subclass label W).2 := by
  have hs := itemNumerator_pos_lt geom hgeom subclass label W hW
  rw [← rawItem_numerator_cast geom hgeom subclass label W hW] at hs
  exact_mod_cast hs

theorem rawItem_ratio {n : ℕ} (geom : ℕ) (hgeom : 0 < geom)
    (subclass : Subclass) (label : Option (Fin n)) (W : ℤ)
    (hW : |(W : ℚ) / geom| ≤ 6) :
    ((rawItem geom subclass label W).1 : ℚ) / (rawItem geom subclass label W).2 =
      encodedSize subclass label ((W : ℚ) / geom) := by
  have hc : ((rawItem geom subclass label W).1 : ℚ) =
      (itemNumerator geom subclass label W : ℚ) := by
    exact_mod_cast rawItem_numerator_cast geom hgeom subclass label W hW
  rw [hc]
  exact itemNumerator_ratio geom hgeom subclass label W

end BinPackingGap.IntegerPackingArithmetic

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_IntegerTreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.IntegerPackingArithmetic

theorem rootOffsetNumerator_cast (side : TreeGeometry.Side) :
    (rootOffsetNumerator side : ℚ) = TreeGeometry.rootOffset side := by
  cases side <;> rfl

theorem geomDenominator_mul_treeLeft (m R D L : ℕ)
    (side : TreeGeometry.Side) (w : List ℕ) (hdepth : w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.left m R D side w =
      (treeLeftNumerator m R D L side w : ℚ) := by
  have hpath := geomDenominator_mul_pathSum m R D L 0 w (by simpa using hdepth)
  simp only [TreeGeometry.left, treeLeftNumerator, Nat.cast_add, Nat.cast_mul,
    rootOffsetNumerator_cast]
  rw [mul_add, hpath]
  ring

theorem geomDenominator_mul_treeRight (m R D L : ℕ)
    (side : TreeGeometry.Side) (w : List ℕ) (hdepth : w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.right m R D side w =
      (treeRightNumerator m R D L side w : ℚ) := by
  have hleft := geomDenominator_mul_treeLeft m R D L side w hdepth
  simp only [TreeGeometry.right, mul_add, hleft, treeRightNumerator, Nat.cast_add]
  by_cases hw : w = []
  · simp [TreeGeometry.width, hw]
  · simp only [TreeGeometry.width, hw, ite_false]
    rw [geomDenominator_mul_lambda m R D L w.length hdepth]

end BinPackingGap.IntegerPackingArithmetic

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryScores
attribute [-instance] _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

abbrev IncidencePosition (v : D.Vertex) := D.graph.IncidencePosition D.R v

abbrev PlusLeaf := {v : D.plus.Node // v.val ∈ D.plus.leaves}
abbrev MinusLeaf := {v : D.minus.Node // v.val ∈ D.minus.leaves}
abbrev TestAt (v : D.Vertex) :=
  D.PlusLeaf ⊕ (D.MinusLeaf ⊕ D.IncidencePosition v)

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData)

def allJobEquiv : (Σ v : D.Vertex, D.JobCopy v) ≃
    ((D.Edge × Fin 2) × Fin D.R) × Fin D.d where
  toFun j := ((j.2.1.1.val, j.2.1.2), j.2.2)
  invFun j := ⟨D.graph.endpoint j.1.1.1 j.1.1.2,
    ((⟨j.1.1, rfl⟩, j.1.2), j.2)⟩
  left_inv := by
    rintro ⟨v, ⟨⟨⟨es, hv⟩, rep⟩, copy⟩⟩
    cases hv
    rfl
  right_inv := by rintro ⟨⟨⟨edge, side⟩, rep⟩, copy⟩; rfl

end InventoryData
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_TestGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def incidencePosition {v : D.Vertex} (j : D.IncidencePosition v) : D.Position :=
  (j.1.val.1, j.2)

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def stateFlagSpecies {v : D.Vertex} : D.LocalBin v → FlagSpecies
  | .inl (.inl _) => .tree
  | .inl (.inr _) => .main
  | .inr _ => .edge

def stateGlobalSpecies {v : D.Vertex} (selected : Bool) :
    D.LocalBin v → GlobalSpecies D.graph
  | .inl b => D.stateMainGlobalSpecies selected b
  | .inr j => .edge (D.jobPosition j).1 (!selected)

abbrev PhysicalBins := Σ v : D.Vertex, D.LocalBin v

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_LocalCompletionCoverage
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.LocalResourceAllocation

open UniformTree

def oppositeTree {d : ℕ} (T : CompetingTrees d) : Bool → UniformTree
  | false => T.plus
  | true => T.minus

def oppositeMarking {d : ℕ} (T : CompetingTrees d) :
    (selected : Bool) → Finset (oppositeTree T selected).Node
  | false => T.markingPlus
  | true => T.markingMinus

abbrev OppositeMarked {d : ℕ} (T : CompetingTrees d) (selected : Bool) :=
  ↥(oppositeMarking T selected)

theorem opposite_height {d : ℕ} (T : CompetingTrees d) (selected : Bool) :
    (oppositeTree T selected).height = T.height := by
  cases selected
  · exact T.plus_height
  · exact T.minus_height

theorem opposite_depth_pos {d : ℕ} (T : CompetingTrees d) (selected : Bool)
    (a : OppositeMarked T selected) : 0 < depth a.val := by
  cases selected
  · exact T.markingPlus_depth_pos a.val a.property
  · exact T.markingMinus_depth_pos a.val a.property

theorem opposite_quota {d : ℕ} (T : CompetingTrees d) (selected : Bool)
    (ell : ℕ) (hlo : 1 ≤ ell) (hhi : ell ≤ T.height) :
    ((oppositeMarking T selected).filter (fun node => depth node = ell)).card ≤
      T.quota ell := by
  cases selected
  · exact T.plus_quota ell hlo hhi
  · exact T.minus_quota ell hlo hhi

variable (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ)

local notation "D" => InventoryData.ofCompetingTrees G T R k

def markedDepth (selected : Bool) (a : OppositeMarked T selected) : (D).Depth :=
  ⟨depth a.val, Finset.mem_Icc.mpr
    ⟨opposite_depth_pos T selected a,
      (depth_le_height a.val).trans_eq (opposite_height T selected)⟩⟩

def markedByDepth (selected : Bool) : OppositeMarked T selected ↪
    Σ ell : (D).Depth,
      ↥((oppositeMarking T selected).filter (fun node => depth node = ell.val)) := by
  classical
  refine ⟨fun a => ⟨markedDepth G T R k selected a,
    ⟨a.val, Finset.mem_filter.mpr ⟨a.property, rfl⟩⟩⟩, ?_⟩
  intro a b hab
  apply Subtype.ext
  exact congrArg (fun z => z.2.val) hab

def markedResource (selected : Bool) : OppositeMarked T selected ↪ (D).PositiveLocal := by
  classical
  exact (markedByDepth G T R k selected).trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl (D).Depth) (fun ell =>
      (Finset.equivFin
        ((oppositeMarking T selected).filter (fun node => depth node = ell.val))).toEmbedding.trans
        (Fin.castLEEmb (opposite_quota T selected ell.val
          (Finset.mem_Icc.mp ell.property).1 (Finset.mem_Icc.mp ell.property).2))))

@[simp] theorem markedResource_depth (selected : Bool) (a : OppositeMarked T selected) :
    (markedResource G T R k selected a).1.val = depth a.val := rfl

def zeroResource (v : G.Vertex) : Fin d ↪ (D).DMAt v := by
  clear hd
  have hstock : d ≤ (D).t - (D).P := by
    have h := (D).two_mul_d_le_t_sub_P
    change 2 * d ≤ (D).t - (D).P at h
    omega
  refine ⟨fun j => .inr (.inl (Fin.castLE hstock j)), ?_⟩
  intro a b hab
  exact Fin.castLE_injective hstock (Sum.inl.inj (Sum.inr.inj hab))

@[simp] theorem zeroResource_local_length (v : G.Vertex) (j : Fin d) :
    (D).localLength (.inl (zeroResource G T R k v j)) = 0 := rfl

end BinPackingGap.LocalResourceAllocation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_InventoryCoverage
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap
namespace InventoryCoverage

variable {D : InventoryData} {I : Instance} {b : ℕ}

def itemRowBaseline (D : InventoryData) : D.Item → ℚ
  | ⟨.x, ⟨_, r⟩⟩ => D.rowBaseline r
  | _ => 0

def itemRowShort (D : InventoryData) : D.Item → Bool
  | ⟨.x, ⟨_, r⟩⟩ => D.rowShort r
  | _ => false

def itemKeyBaseline (D : InventoryData) : D.Item → ℚ
  | ⟨.anchor, ⟨_, .inr j⟩⟩ => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)
  | _ => 0

def itemDeadline (D : InventoryData) : D.Item → ℚ
  | ⟨.anchor, ⟨_, .inl z⟩⟩ => D.deadline z
  | _ => 0

def rowBaseline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemRowBaseline D ∘ e.symm

def rowShort (e : D.Item ≃ I.Item) : I.Item → Bool := itemRowShort D ∘ e.symm

def keyBaseline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemKeyBaseline D ∘ e.symm

def anchorDeadline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemDeadline D ∘ e.symm

def treePrefix (D : InventoryData) (a : ℚ) : Finset D.TreeRow :=
  Finset.univ.filter fun r => D.treeBaseline r ≤ a

def jobPrefix (D : InventoryData) (v : D.Vertex) (a : ℚ) : Finset (D.JobCopy v) :=
  Finset.univ.filter fun j => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) ≤ a

def originalBaselinePrefix (D : InventoryData) (v : D.Vertex) (a : ℚ) :
    Finset (D.MBase v) := Finset.univ.filter fun z => D.mainBaseline z ≤ a

def jobsAt (D : InventoryData) (v : D.Vertex) (current : ℚ) : Finset (D.JobCopy v) :=
  Finset.univ.filter fun j =>
    Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) = current

def positionOf (D : InventoryData) {v : D.Vertex} (r : D.IncidencePosition v) : D.Position :=
  D.incidencePosition r

end InventoryCoverage
end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PhaseIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

def buildAuxiliary : (n : ℕ) → AuxiliaryTree n
  | 0 => AuxiliaryTree.initial
  | n + 1 => (buildAuxiliary n).step

@[simp] theorem buildAuxiliary_zero : buildAuxiliary 0 = AuxiliaryTree.initial := rfl

@[simp] theorem buildAuxiliary_succ (n : ℕ) :
    buildAuxiliary (n + 1) = (buildAuxiliary n).step := rfl

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Trees_CompetingTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

def competingTrees (d : ℕ) (hd : 0 < d) : CompetingTrees d :=
  CompetingTrees.ofAuxiliary d hd (buildAuxiliary (2 * d - 1))

end BinPackingGap

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_ExtractedCover
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.SideChoice

open UniformTree

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable {d : ℕ} (T : CompetingTrees d)

def marksPlus (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) : Finset T.plus.Node := by
  classical
  exact Finset.univ.filter fun v => ∃ t ∈ selected, hits t (.inl v)

def marksMinus (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) : Finset T.minus.Node := by
  classical
  exact Finset.univ.filter fun v => ∃ t ∈ selected, hits t (.inr v)

omit [DecidableEq α] in
@[simp] theorem mem_marksPlus [DecidableEq α] (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) (v : T.plus.Node) :
    v ∈ marksPlus T selected hits ↔ ∃ t ∈ selected, hits t (.inl v) := by
  classical
  simp [marksPlus]

omit [DecidableEq α] in
@[simp] theorem mem_marksMinus [DecidableEq α] (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) (v : T.minus.Node) :
    v ∈ marksMinus T selected hits ↔ ∃ t ∈ selected, hits t (.inr v) := by
  classical
  simp [marksMinus]

end BinPackingGap.SideChoice

namespace BinPackingGap

section

def reductionTrees (c : ℕ) (ρ : ℝ) : CompetingTrees (depthDemand c ρ) :=
  competingTrees (depthDemand c ρ) (depthDemand_pos c ρ)

def reductionInventory (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : InventoryData :=
  InventoryData.ofCompetingTrees G (reductionTrees c ρ)
    (repetitions (reductionTrees c ρ).quotaTotal G.n (lossAllowance c)) k

def reductionBinBound (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : ℕ :=
  (reductionInventory c ρ G k).B

@[simp] theorem reductionInventory_graph (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).graph = G := rfl

@[simp] theorem reductionInventory_d (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).d = depthDemand c ρ := rfl

@[simp] theorem reductionInventory_k (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).k = k := rfl

@[simp] theorem reductionInventory_P (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).P = (reductionTrees c ρ).quotaTotal := rfl

open UniformTree

end

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingScalarExpression
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open IntegerPackingArithmetic

variable (D : InventoryData)

theorem coordinateDenominator_pos : 0 < D.coordinateDenominator :=
  geomDenominator_pos _ _ _ _

end BinPackingGap.InventoryData

namespace BinPackingGap.NaturalPackingNumerator

open IntegerPackingArithmetic

theorem numeratorParts_toNat {n : Nat} (geom : Nat) (subclass : Subclass)
    (label : Option (Fin n)) (W : NatDifference) :
    (numeratorParts geom subclass label W).toNat = (itemNumerator geom subclass label W.eval).toNat := by
  rw [NatDifference.toNat_eq, eval_numeratorParts]

def inventoryParts (D : InventoryData) (i : D.Item) : NatDifference :=
  numeratorParts D.coordinateDenominator (D.itemSubclass i) (D.itemLabel i)
    (coordinateParts D i)

def inventoryNumerator (D : InventoryData) (i : D.Item) : Nat :=
  (inventoryParts D i).toNat

theorem inventoryNumerator_eq (D : InventoryData) (i : D.Item) :
    inventoryNumerator D i =
      (itemNumerator D.coordinateDenominator (D.itemSubclass i) (D.itemLabel i)
        (D.itemIntegerCoordinate i)).toNat := by
  simp only [inventoryNumerator, inventoryParts, numeratorParts_toNat, eval_coordinateParts]

def naturalRawItem (D : InventoryData) (i : D.Item) : Nat × Nat :=
  (inventoryNumerator D i, sizeDenominator D.graph.n D.coordinateDenominator)

theorem naturalRawItem_eq (D : InventoryData) (i : D.Item) :
    naturalRawItem D i = D.itemRawPair i := by
  simp only [naturalRawItem, InventoryData.itemRawPair, rawItem, inventoryNumerator_eq]

end BinPackingGap.NaturalPackingNumerator

namespace BinPackingGap.PackingCoordinateExpression

open IntegerPackingArithmetic
open NaturalPackingNumerator
open NatExpressionCompiler

instance instFintypeTreeDescriptor (plus minus : UniformTree) : Fintype (TreeDescriptor plus minus) where
  elems := Finset.univ.image TreeDescriptor.plusNode ∪
    Finset.univ.image TreeDescriptor.minusNode ∪ {.padding}
  complete tree := by cases tree <;> simp

instance instFintypeDescriptor (plus minus : UniformTree) (L : Nat) : Fintype (Descriptor plus minus L) where
  elems := Finset.univ.image Descriptor.treeRow ∪
    Finset.univ.image Descriptor.jobRow ∪
    Finset.univ.image Descriptor.treeAnchor ∪
    {.jobAnchor, .jobKey, .zero} ∪
    Finset.univ.image Descriptor.globalUnit ∪
    Finset.univ.image Descriptor.globalEdge ∪
    Finset.univ.image Descriptor.localDepth
  complete descriptor := by cases descriptor <;> simp

def coordinateDescriptor (D : InventoryData) : D.Item → Descriptor D.plus D.minus D.L
  | ⟨.x, ⟨_, .inl tree⟩⟩ => .treeRow (treeDescriptor D tree)
  | ⟨.x, ⟨_, .inr (short, _)⟩⟩ => .jobRow short
  | ⟨.anchor, ⟨_, .inl (.inl tree)⟩⟩ => .treeAnchor (treeDescriptor D tree)
  | ⟨.anchor, ⟨_, .inl (.inr _)⟩⟩ => .jobAnchor
  | ⟨.anchor, ⟨_, .inr _⟩⟩ => .jobKey
  | ⟨.«global», ⟨.up one, _⟩⟩ => .globalUnit one
  | ⟨.«global», ⟨.um one, _⟩⟩ => .globalUnit one
  | ⟨.«global», ⟨.edge _ permit, _⟩⟩ => .globalEdge permit
  | ⟨.«local», ⟨_, .inl (.inl ⟨depth, _⟩)⟩⟩ =>
      .localDepth ⟨depth.val, Nat.lt_succ_of_le (Finset.mem_Icc.mp depth.property).2⟩
  | ⟨.«local», _⟩ => .zero
  | ⟨.flag, _⟩ => .zero

def edgeIndex (D : InventoryData) : D.Item → Nat
  | ⟨.x, ⟨_, .inr (_, job)⟩⟩ => (D.jobPosition job).1.val
  | ⟨.anchor, ⟨_, .inl (.inr job)⟩⟩ => (D.jobPosition job).1.val
  | ⟨.anchor, ⟨_, .inr job⟩⟩ => (D.jobPosition job).1.val
  | ⟨.«global», ⟨.edge edge _, _⟩⟩ => edge.val
  | _ => 0

def repetitionOne (D : InventoryData) : D.Item → Nat
  | ⟨.x, ⟨_, .inr (_, job)⟩⟩ => (D.jobPosition job).2.val + 1
  | ⟨.anchor, ⟨_, .inl (.inr job)⟩⟩ => (D.jobPosition job).2.val + 1
  | ⟨.anchor, ⟨_, .inr job⟩⟩ => (D.jobPosition job).2.val + 1
  | _ => 0

def coordinateValues (D : InventoryData) (i : D.Item) : Input → Nat :=
  registers D (edgeIndex D i) (repetitionOne D i)

theorem eval_coordinateDescriptor (D : InventoryData) (i : D.Item) :
    (expression D.geometryBound (coordinateDescriptor D i)).eval (coordinateValues D i) =
      coordinateParts D i := by
  rcases i with ⟨role, i⟩
  cases role with
  | x =>
      rcases i with ⟨v, tree | ⟨short, job⟩⟩
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, rowParts, rowBaselineParts, InventoryData.rowShort]
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, rowParts, rowBaselineParts, InventoryData.rowShort, baselineParts]
        rfl
  | anchor =>
      rcases i with ⟨v, (tree | job) | job⟩
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, anchorParts, deadlineParts]
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, anchorParts, deadlineParts, baselineParts]
      · simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, anchorParts, baselineParts, betaParts]
  | «global» =>
      rcases i with ⟨species, copy⟩
      cases species with
      | up one => cases one <;> simp [coordinateDescriptor, expression, coordinateValues, edgeIndex,
          repetitionOne, coordinateParts, globalParts, registers]
      | um one => cases one <;> simp [coordinateDescriptor, expression, coordinateValues, edgeIndex,
          repetitionOne, coordinateParts, globalParts, registers]
      | edge edge permit => simp [coordinateDescriptor, expression, coordinateValues, edgeIndex, repetitionOne,
          coordinateParts, globalParts, betaParts]
  | «local» =>
      rcases i with ⟨v, (⟨depth, copy⟩ | (zero | job)) | job⟩ <;>
        simp [coordinateDescriptor, expression, coordinateParts, localParts]
  | flag => simp [coordinateDescriptor, expression, coordinateParts]

end BinPackingGap.PackingCoordinateExpression

namespace BinPackingGap.PackingScalarExpression

open NatExpressionCompiler NaturalPackingNumerator IntegerPackingArithmetic

def values {n : Nat} (geom : Nat) (label : Option (Fin n)) (W : NatDifference) :
    Variable → Nat
  | .vertexPower => 3 ^ n
  | .geometry => geom
  | .labelPower => NaturalPackingNumerator.labelPower label
  | .coordinatePositive => W.pos
  | .coordinateNegative => W.neg

def positiveLabel (subclass : Subclass) : Expr Variable :=
  match subclass.role with
  | .x => .input .labelPower
  | .«local» => .input .labelPower
  | _ => .constant 0

def positiveTerm (subclass : Subclass) : Expr Variable :=
  .add (.add (.add baseTerm
    (.mul primaryFactor (.constant (primaryParts subclass).pos)))
    (.mul secondaryFactor (positiveLabel subclass))) (.input .coordinatePositive)

def numerator (subclass : Subclass) : Expr Variable :=
  .monus (positiveTerm subclass) (negativeTerm subclass)

theorem eval_positiveLabel {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (positiveLabel subclass) = (secondaryParts subclass label).pos := by
  cases h : subclass.role <;>
    simp [positiveLabel, secondaryParts, h, values, NatDifference.ofNat,
      NatDifference.negate]

theorem eval_negativeLabel {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (negativeLabel subclass) = (secondaryParts subclass label).neg := by
  cases h : subclass.role <;>
    simp [negativeLabel, secondaryParts, h, eval, values, NatDifference.ofNat,
      NatDifference.negate]

theorem eval_positiveTerm {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (positiveTerm subclass) =
      (numeratorParts geom subclass label W).pos := by
  simp only [positiveTerm, eval_add, eval_mul, eval_constant, eval_input,
    eval_positiveLabel, numeratorParts, signedParts_pos]
  rfl

theorem eval_negativeTerm {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (negativeTerm subclass) =
      (numeratorParts geom subclass label W).neg := by
  simp only [negativeTerm, eval_add, eval_mul, eval_constant, eval_input,
    eval_negativeLabel, numeratorParts, signedParts_neg]
  rfl

theorem eval_numerator {n : Nat} (geom : Nat) (label : Option (Fin n))
    (W : NatDifference) (subclass : Subclass) :
    eval (values geom label W) (numerator subclass) =
      (numeratorParts geom subclass label W).toNat := by
  simp only [numerator, eval_monus, eval_positiveTerm, eval_negativeTerm,
    NatDifference.toNat]

end BinPackingGap.PackingScalarExpression

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def rawItemList : RawInstance := D.itemList.map D.itemRawPair

theorem rawItemList_length_items : D.rawItemList.length = D.itemList.length := by
  simp [rawItemList]

def rawItemListEquiv (hk : D.k ≤ D.graph.n) : Fin D.rawItemList.length ≃ D.Item :=
  (finCongr D.rawItemList_length_items).trans (D.itemListEquiv hk)

@[simp] theorem rawItemListEquiv_apply (hk : D.k ≤ D.graph.n)
    (i : Fin D.rawItemList.length) :
    D.rawItemListEquiv hk i =
      D.itemList.get (Fin.cast D.rawItemList_length_items i) := rfl

def rawOutput : RawReductionOutput := (D.B, D.rawItemList)

@[simp] theorem rawOutput_bins : D.rawOutput.1 = D.B := rfl

@[simp] theorem rawOutput_items : D.rawOutput.2 = D.rawItemList := rfl

end BinPackingGap.InventoryData

namespace BinPackingGap

def graphPackingOutput (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) : RawReductionOutput :=
  (reductionInventory c ρ x.graph x.k).rawOutput

@[simp] theorem graphPackingOutput_bins (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    (graphPackingOutput c ρ x).1 = reductionBinBound c ρ x.graph x.k := rfl

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PackingInventoryDescriptors
attribute [-instance] _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingInventoryDescriptors

open PackingCoordinateExpression NaturalPackingNumerator IntegerPackingArithmetic

variable (D : InventoryData)

abbrev ItemDescriptor := Subclass × Descriptor D.plus D.minus D.L

def itemDescriptor (i : D.Item) : ItemDescriptor D :=
  (D.itemSubclass i, coordinateDescriptor D i)

def positiveDescriptor (r : D.PositiveLocal) : ItemDescriptor D :=
  (.dm, .localDepth ⟨r.1.val, Nat.lt_succ_of_le (Finset.mem_Icc.mp r.1.property).2⟩)

def vertexDescriptors : List (ItemDescriptor D) :=
  (D.treeRowList.map fun r => (D.treeSubclass r, .treeRow (treeDescriptor D r))) ++
  (D.treeRowList.map fun r => (.z, .treeAnchor (treeDescriptor D r))) ++
  (D.positiveLocalList.map (positiveDescriptor D)) ++
  ((List.finRange (D.t - D.P)).map fun _ => (.dm, .zero))

def jobDescriptors : List (ItemDescriptor D) :=
  ((List.finRange D.d).map fun _ => (.s, .jobRow true)) ++
  ((List.finRange D.d).map fun _ => (.s, .jobRow false)) ++
  ((List.finRange D.d).map fun _ => (.z, .jobAnchor)) ++
  ((List.finRange D.d).map fun _ => (.y, .jobKey)) ++
  ((List.finRange D.d).map fun _ => (.dm, .zero)) ++
  ((List.finRange D.d).map fun _ => (.dg, .zero))

theorem vertexChunk_descriptors (v : D.Vertex) :
    (D.vertexChunk v).map (itemDescriptor D) = vertexDescriptors D := by
  simp [InventoryData.vertexChunk, vertexDescriptors, itemDescriptor,
    List.map_append, List.map_map, Function.comp_def, InventoryData.itemSubclass,
    InventoryData.rowSubclass, coordinateDescriptor, positiveDescriptor]

theorem jobChunk_descriptors (e : D.Edge) (j : Fin D.R) (s : Fin 2) :
    (D.jobChunk e j s).map (itemDescriptor D) = jobDescriptors D := by
  simp [InventoryData.jobChunk, jobDescriptors, itemDescriptor, List.map_append,
    List.map_map, Function.comp_def, InventoryData.itemSubclass, InventoryData.rowSubclass,
    coordinateDescriptor]

def rawOfDescriptor (label : Option D.Vertex) (edge rep : Nat)
    (descriptor : ItemDescriptor D) : Nat × Nat :=
  ((numeratorParts D.coordinateDenominator descriptor.1 label
      ((expression D.geometryBound descriptor.2).eval (registers D edge rep))).toNat,
    sizeDenominator D.graph.n D.coordinateDenominator)

theorem rawOfDescriptor_item (i : D.Item) :
    rawOfDescriptor D (D.itemLabel i) (edgeIndex D i) (repetitionOne D i)
      (itemDescriptor D i) = D.itemRawPair i := by
  unfold rawOfDescriptor itemDescriptor
  rw [← coordinateValues, eval_coordinateDescriptor]
  exact naturalRawItem_eq D i

theorem vertexChunk_raw (v : D.Vertex) :
    (D.vertexChunk v).map D.itemRawPair =
      (vertexDescriptors D).map (rawOfDescriptor D (some v) 0 0) := by
  rw [← vertexChunk_descriptors D v, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hraw := rawOfDescriptor_item D i
  have hlabel : D.itemLabel i = some v := by
    simp only [InventoryData.vertexChunk, List.mem_append, List.mem_map, or_assoc] at hi
    rcases hi with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> rfl
  have hedge : edgeIndex D i = 0 := by
    simp only [InventoryData.vertexChunk, List.mem_append, List.mem_map, or_assoc] at hi
    rcases hi with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> rfl
  have hrep : repetitionOne D i = 0 := by
    simp only [InventoryData.vertexChunk, List.mem_append, List.mem_map, or_assoc] at hi
    rcases hi with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> rfl
  simpa only [Function.comp_apply, hlabel, hedge, hrep] using hraw.symm

theorem jobChunk_raw (e : D.Edge) (j : Fin D.R) (s : Fin 2) :
    (D.jobChunk e j s).map D.itemRawPair =
      (jobDescriptors D).map
        (rawOfDescriptor D (some (D.graph.endpoint e s)) e.val (j.val + 1)) := by
  rw [← jobChunk_descriptors D e j s, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [InventoryData.jobChunk, List.mem_append, List.mem_map, or_assoc] at hi
  rcases hi with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ |
    ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  all_goals
    rw [← naturalRawItem_eq]
    simp [naturalRawItem, inventoryNumerator, inventoryParts,
      rawOfDescriptor, itemDescriptor, InventoryData.itemSubclass,
      InventoryData.rowSubclass, InventoryData.itemLabel, InventoryData.jobPosition,
      InventoryData.listedJobCopy, coordinateDescriptor, expression, coordinateParts,
      rowParts, rowBaselineParts, anchorParts, deadlineParts, localParts,
      InventoryData.rowShort, Parts.eval, Parts.ofExpr, Parts.sub, Parts.negate,
      registers, baselineExpr, betaExpr, baselineParts, betaParts, NatExpressionCompiler.eval,
      NatDifference.ofNat, NatDifference.sub, NatDifference.negate]

def globalDescriptor : GlobalSpecies D.graph → ItemDescriptor D
  | .up one => (.up, .globalUnit one)
  | .um one => (.um, .globalUnit one)
  | .edge _ permit => (.w, .globalEdge permit)

def globalEdgeIndex : GlobalSpecies D.graph → Nat
  | .edge e _ => e.val
  | _ => 0

def flagDescriptor : FlagSpecies → ItemDescriptor D
  | .tree => (.ft, .zero)
  | .main => (.fm, .zero)
  | .edge => (.fg, .zero)

theorem globalPool_raw (species : GlobalSpecies D.graph) :
    (D.globalPool species).map D.itemRawPair =
      (List.finRange (D.globalStock species)).map
        (fun _ => rawOfDescriptor D none (globalEdgeIndex D species) 0
          (globalDescriptor D species)) := by
  unfold InventoryData.globalPool
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  have h := rawOfDescriptor_item D ⟨.«global», ⟨species, j⟩⟩
  cases species <;> simpa only [itemDescriptor, InventoryData.itemLabel,
    InventoryData.itemSubclass, coordinateDescriptor, edgeIndex, repetitionOne,
    globalDescriptor, globalEdgeIndex, Function.comp_apply] using h.symm

theorem flagPool_raw (species : FlagSpecies) :
    (D.flagPool species).map D.itemRawPair =
      (List.finRange (D.flagStock species)).map
        (fun _ => rawOfDescriptor D none 0 0 (flagDescriptor D species)) := by
  unfold InventoryData.flagPool
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  have h := rawOfDescriptor_item D ⟨.flag, ⟨species, j⟩⟩
  cases species <;> simpa only [itemDescriptor, InventoryData.itemLabel,
    InventoryData.itemSubclass, coordinateDescriptor, edgeIndex, repetitionOne,
    flagDescriptor, Function.comp_apply] using h.symm

def vertexStream : RawInstance :=
  (List.finRange D.graph.n).flatMap fun v =>
    (vertexDescriptors D).map (rawOfDescriptor D (some v) 0 0)

def jobStream : RawInstance :=
  (List.finRange D.graph.edges.length).flatMap fun e =>
    (List.finRange D.R).flatMap fun j =>
      (List.finRange 2).flatMap fun s =>
        (jobDescriptors D).map
          (rawOfDescriptor D (some (D.graph.endpoint e s)) e.val (j.val + 1))

def globalPoolStream (species : GlobalSpecies D.graph) : RawInstance :=
  (List.finRange (D.globalStock species)).map
    (fun _ => rawOfDescriptor D none (globalEdgeIndex D species) 0
      (globalDescriptor D species))

def globalStream : RawInstance :=
  globalPoolStream D (.up true) ++ globalPoolStream D (.up false) ++
    globalPoolStream D (.um true) ++ globalPoolStream D (.um false) ++
    (List.finRange D.graph.edges.length).flatMap fun e =>
      globalPoolStream D (.edge e true) ++ globalPoolStream D (.edge e false)

def flagPoolStream (species : FlagSpecies) : RawInstance :=
  (List.finRange (D.flagStock species)).map
    (fun _ => rawOfDescriptor D none 0 0 (flagDescriptor D species))

def flagStream : RawInstance :=
  flagPoolStream D .tree ++ flagPoolStream D .main ++ flagPoolStream D .edge

def recipeStream : RawInstance :=
  vertexStream D ++ jobStream D ++ globalStream D ++ flagStream D

theorem recipeStream_eq_rawItemList : recipeStream D = D.rawItemList := by
  simp only [InventoryData.rawItemList, InventoryData.itemList, List.map_append,
    InventoryData.vertexItems, InventoryData.jobItems, InventoryData.globalItems,
    InventoryData.flagItems, List.map_flatMap, vertexChunk_raw, jobChunk_raw,
    globalPool_raw, flagPool_raw, recipeStream, vertexStream, jobStream, globalStream,
    flagStream, globalPoolStream, flagPoolStream]

end BinPackingGap.PackingInventoryDescriptors

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingCountedProgram
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype _root_.OAI.BinPackingGap.instFintypeGlobalSpecies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.GraphFieldMachine

open Turing
open BinaryEncoding
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open GraphTallyMachine (Mode Slot afterName initial transition)

def emit : Field → Mode → Bool → List Bool
  | .threshold, .name .header, bit => [bit]
  | .threshold, .digit .header, bit => [bit]
  | .endpoints, .endpoints, bit => [bit]
  | .endpoints, .name .edgeFirst, bit => [bit]
  | .endpoints, .digit .edgeFirst, bit => [bit]
  | .endpoints, .name .edgeSecond, bit => [bit]
  | .endpoints, .digit .edgeSecond, bit => [bit]
  | _, _, _ => []

def scanOutput (field : Field) : Mode → List Bool → List Bool :=
  MachineTransducer.output transition (emit field)

@[simp] theorem scanOutput_nil (field : Field) (mode : Mode) :
    scanOutput field mode [] = [] := rfl

theorem scanOutput_cons (field : Field) (mode : Mode) (bit : Bool) (rest : List Bool) :
    scanOutput field mode (bit :: rest) =
      emit field mode bit ++ scanOutput field (transition mode bit) rest := rfl

theorem scanOutput_frame (field : Field) (slot : Slot) (bits suffix : List Bool) :
    scanOutput field (.name slot)
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) =
      (if keepsName field slot then BinPackingCompleteness.BinaryEncoding.frame bits else []) ++
        scanOutput field (afterName slot) suffix := by
  induction bits with
  | nil => cases field <;> cases slot <;> rfl
  | cons bit bits ih =>
      cases field <;> cases slot <;>
        simp [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
          scanOutput_cons, transition, emit, keepsName, afterName, ih]

theorem scanOutput_natBits (field : Field) (slot : Slot) (n : Nat) (suffix : List Bool) :
    scanOutput field (.name slot) (natBits n ++ suffix) =
      (if keepsName field slot then natBits n else []) ++
        scanOutput field (afterName slot) suffix :=
  scanOutput_frame field slot n.bits suffix

theorem scanOutput_pairBits (field : Field) (edge : Nat × Nat) (suffix : List Bool) :
    scanOutput field (.name .edgeFirst) (pairBits natBits natBits edge ++ suffix) =
      (if field = .endpoints then pairBits natBits natBits edge else []) ++
        scanOutput field .endpoints suffix := by
  cases field <;>
    simp [pairBits, List.append_assoc, scanOutput_natBits, keepsName, afterName]

theorem scanOutput_vertices (field : Field) (vertices : List Nat) (suffix : List Bool) :
    scanOutput field .vertices (listBits natBits vertices ++ suffix) =
      scanOutput field .endpoints suffix := by
  induction vertices with
  | nil => cases field <;> rfl
  | cons vertex vertices ih =>
      cases field <;>
        simp [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
          transition, emit, scanOutput_natBits, keepsName, afterName, ih]

theorem scanOutput_endpoints (field : Field) (endpoints : List (Nat × Nat))
    (suffix : List Bool) :
    scanOutput field .endpoints (listBits (pairBits natBits natBits) endpoints ++ suffix) =
      (if field = .endpoints then listBits (pairBits natBits natBits) endpoints else []) ++
        scanOutput field .done suffix := by
  induction endpoints with
  | nil => cases field <;> rfl
  | cons edge endpoints ih =>
      cases field <;>
        simp [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
          transition, emit, scanOutput_pairBits, ih]

def fieldsOutput : Field → GraphFields → List Bool
  | .threshold, fields => natBits fields.k
  | .endpoints, fields => listBits (pairBits natBits natBits) fields.endpoints

def fieldBits (field : Field) (input : GraphReductionInput) : List Bool :=
  fieldsOutput field input.fields

@[simp] theorem thresholdBits (input : GraphReductionInput) :
    fieldBits .threshold input = natBits input.k := rfl

@[simp] theorem endpointsBits (input : GraphReductionInput) :
    fieldBits .endpoints input =
      listBits (pairBits natBits natBits) input.graph.endpointPairs := rfl

theorem output_graphFields (field : Field) (fields : GraphFields) :
    scanOutput field initial fields.bits = fieldsOutput field fields := by
  have hend := scanOutput_endpoints field fields.endpoints []
  simp only [List.append_nil, scanOutput_nil] at hend
  cases field <;>
    simp [GraphFields.bits, List.append_assoc, initial, scanOutput_natBits,
      keepsName, afterName, scanOutput_vertices, fieldsOutput, hend]

theorem output_graphBits (field : Field) (input : GraphReductionInput) :
    scanOutput field initial (graphBits input) = fieldBits field input :=
  output_graphFields field input.fields

theorem emit_length_le (field : Field) (mode : Mode) (bit : Bool) :
    (emit field mode bit).length ≤ 1 := by
  cases mode with
  | vertices => cases field <;> simp [emit]
  | endpoints => cases field <;> simp [emit]
  | name slot => cases field <;> cases slot <;> simp [emit]
  | digit slot => cases field <;> cases slot <;> simp [emit]
  | done => cases field <;> simp [emit]

theorem scanOutput_length_le (field : Field) (mode : Mode) (input : List Bool) :
    (scanOutput field mode input).length ≤ input.length := by
  induction input generalizing mode with
  | nil => exact Nat.le_refl _
  | cons bit input ih =>
      rw [scanOutput_cons, List.length_append, List.length_cons]
      have he := emit_length_le field mode bit
      have hi := ih (transition mode bit)
      omega

theorem fieldBits_length_le (field : Field) (input : GraphReductionInput) :
    (fieldBits field input).length ≤ (graphBits input).length := by
  rw [← output_graphBits]
  exact scanOutput_length_le field initial (graphBits input)

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := MachineTransducerCopy.State σ Mode

def clean (ambient : σ) : State σ := ((ambient, initial), none)

inductive Label
  | scan | restore | transfer
  | emitter (mode : Mode) (bit : Bool)
  deriving DecidableEq, Fintype

def instruction (field : Field) (slots : Fin 4 ↪ K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 1) initial
      (fun mode bit => labels (.emitter mode bit)) (labels .restore)
  | .emitter mode bit => MachineTransducerCopy.emitter (slots 2) transition (emit field)
      (labels .scan) mode bit
  | .restore => MachineTransfer.loopAt (slots 1) (slots 0) id false
      (labels .restore) (some (labels .transfer))
  | .transfer => MachineTransfer.loopAt (slots 2) (slots 3) id false
      (labels .transfer) exit

def resultTapes (field : Field) (slots : Fin 4 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) : K → List Bool :=
  Function.update base (slots 3) (fieldBits field input ++ base (slots 3))

def steps (field : Field) (input : GraphReductionInput) : Nat :=
  (3 * (graphBits input).length + 2) + ((fieldBits field input).length + 1)

theorem steps_le (field : Field) (input : GraphReductionInput) :
    steps field input ≤ 4 * (graphBits input).length + 3 := by
  have h := fieldBits_length_le field input
  unfold steps
  omega

end BinPackingGap.GraphFieldMachine

namespace BinPackingGap.GraphTokenMachine

open Turing
open BinaryEncoding
open BinPackingGames.Foundations.Complexity
open BinPackingGames.Reduction
open GraphTallyMachine (Mode Slot afterName initial transition)

instance instFintypeField : Fintype Field where
  elems := {.vertex, .edge}
  complete field := by cases field <;> simp

def emit : Field → Mode → Bool → List Bool
  | .vertex, .vertices, true => [true]
  | .edge, .endpoints, true => [true]
  | _, _, _ => []

def scanOutput (field : Field) : Mode → List Bool → List Bool :=
  MachineTransducer.output transition (emit field)

@[simp] theorem scanOutput_nil (field : Field) (mode : Mode) :
    scanOutput field mode [] = [] := rfl

theorem scanOutput_cons (field : Field) (mode : Mode) (bit : Bool) (rest : List Bool) :
    scanOutput field mode (bit :: rest) =
      emit field mode bit ++ scanOutput field (transition mode bit) rest := rfl

theorem scanOutput_frame (field : Field) (slot : Slot) (bits suffix : List Bool) :
    scanOutput field (.name slot)
        (BinPackingCompleteness.BinaryEncoding.frame bits ++ suffix) =
      scanOutput field (afterName slot) suffix := by
  induction bits with
  | nil => cases field <;> rfl
  | cons bit bits ih =>
      cases field <;>
        simpa only [BinPackingCompleteness.BinaryEncoding.frame, List.cons_append,
          scanOutput_cons, transition, emit, List.nil_append] using ih

theorem scanOutput_natBits (field : Field) (slot : Slot) (n : Nat) (suffix : List Bool) :
    scanOutput field (.name slot) (natBits n ++ suffix) =
      scanOutput field (afterName slot) suffix :=
  scanOutput_frame field slot n.bits suffix

theorem scanOutput_pairBits (field : Field) (edge : Nat × Nat) (suffix : List Bool) :
    scanOutput field (.name .edgeFirst) (pairBits natBits natBits edge ++ suffix) =
      scanOutput field .endpoints suffix := by
  simp only [pairBits, List.append_assoc, scanOutput_natBits, afterName]

theorem scanOutput_vertices (field : Field) (vertices : List Nat) (suffix : List Bool) :
    scanOutput field .vertices (listBits natBits vertices ++ suffix) =
      (if field = .vertex then List.replicate vertices.length true else []) ++
        scanOutput field .endpoints suffix := by
  induction vertices with
  | nil => cases field <;> rfl
  | cons vertex vertices ih =>
      cases field <;>
        simp [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
          transition, emit, scanOutput_natBits, afterName, ih, List.replicate_succ]

theorem scanOutput_endpoints (field : Field) (endpoints : List (Nat × Nat))
    (suffix : List Bool) :
    scanOutput field .endpoints (listBits (pairBits natBits natBits) endpoints ++ suffix) =
      (if field = .edge then List.replicate endpoints.length true else []) ++
        scanOutput field .done suffix := by
  induction endpoints with
  | nil => cases field <;> rfl
  | cons edge endpoints ih =>
      cases field <;>
        simp [listBits, List.cons_append, List.append_assoc, scanOutput_cons,
          transition, emit, scanOutput_pairBits, ih, List.replicate_succ]

def fieldsCount : Field → GraphFields → Nat
  | .vertex, fields => fields.vertices.length
  | .edge, fields => fields.endpoints.length

def count : Field → GraphReductionInput → Nat
  | .vertex, input => input.graph.n
  | .edge, input => input.graph.edges.length

def tokenBits (field : Field) (input : GraphReductionInput) : List Bool :=
  List.replicate (count field input) true

@[simp] theorem count_vertex (input : GraphReductionInput) :
    count .vertex input = input.graph.n := rfl

@[simp] theorem count_edge (input : GraphReductionInput) :
    count .edge input = input.graph.edges.length := rfl

@[simp] theorem tokenBits_length (field : Field) (input : GraphReductionInput) :
    (tokenBits field input).length = count field input := by simp [tokenBits]

@[simp] theorem tokenBits_reverse (field : Field) (input : GraphReductionInput) :
    (tokenBits field input).reverse = tokenBits field input := by simp [tokenBits]

theorem output_graphFields (field : Field) (fields : GraphFields) :
    scanOutput field initial fields.bits = List.replicate (fieldsCount field fields) true := by
  have hend := scanOutput_endpoints field fields.endpoints []
  simp only [List.append_nil, scanOutput_nil] at hend
  cases field <;>
    simp [GraphFields.bits, List.append_assoc, initial, scanOutput_natBits,
      afterName, scanOutput_vertices, fieldsCount, hend]

theorem fieldsCount_fields (field : Field) (input : GraphReductionInput) :
    fieldsCount field input.fields = count field input := by
  cases field <;> simp [fieldsCount, count, GraphReductionInput.fields]

theorem output_graphBits (field : Field) (input : GraphReductionInput) :
    scanOutput field initial (graphBits input) = tokenBits field input := by
  simpa only [graphBits, fieldsCount_fields, tokenBits] using
    output_graphFields field input.fields

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := MachineTransducerCopy.State σ Mode

def clean (ambient : σ) : State σ := ((ambient, initial), none)

inductive Label
  | scan
  | restore
  | emitter (mode : Mode) (bit : Bool)
  deriving DecidableEq, Fintype

def instruction (field : Field) (slots : Fin 3 ↪ K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (MachineTransducerCopy.Alphabet K) Λ (State σ)
  | .scan => MachineTransducerCopy.scanLoop (slots 0) (slots 1) initial
      (fun mode bit => labels (.emitter mode bit)) (labels .restore)
  | .emitter mode bit => MachineTransducerCopy.emitter (slots 2) transition (emit field)
      (labels .scan) mode bit
  | .restore => MachineTransfer.loopAt (slots 1) (slots 0) id false
      (labels .restore) exit

def resultTapes (field : Field) (slots : Fin 3 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) : K → List Bool :=
  Function.update base (slots 2) (tokenBits field input ++ base (slots 2))

@[simp] theorem resultTapes_destination (field : Field) (slots : Fin 3 ↪ K)
    (base : K → List Bool) (input : GraphReductionInput) :
    resultTapes field slots base input (slots 2) = tokenBits field input ++ base (slots 2) := by
  simp [resultTapes]

end BinPackingGap.GraphTokenMachine

namespace BinPackingGap.GraphPreparationMachine

open Turing
open BinPackingGames.Foundations.Complexity

abbrev State (A : Type) := GraphFieldMachine.State A

inductive Label
  | threshold (label : GraphFieldMachine.Label)
  | endpoints (label : GraphFieldMachine.Label)
  | vertices (label : GraphTokenMachine.Label)
  | edges (label : GraphTokenMachine.Label)
  deriving DecidableEq, Fintype

variable {K Λ A : Type} [DecidableEq K]

omit [DecidableEq K] in
@[simp] theorem fieldSlots_zero [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    fieldSlots slots edge 0 = slots 0 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem fieldSlots_one [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    fieldSlots slots edge 1 = slots 1 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem fieldSlots_two [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    fieldSlots slots edge 2 = slots 2 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem fieldSlots_three [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    fieldSlots slots edge 3 = slots (if edge then 4 else 3) := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem tokenSlots_zero [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    tokenSlots slots edge 0 = slots 0 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem tokenSlots_one [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    tokenSlots slots edge 1 = slots 1 := by cases edge <;> rfl

omit [DecidableEq K] in
@[simp] theorem tokenSlots_two [DecidableEq K] (slots : Fin 7 ↪ K) (edge : Bool) :
    tokenSlots slots edge 2 = slots (if edge then 6 else 5) := by cases edge <;> rfl

def instruction (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (fun _ : K => Bool) Λ (State A)
  | .threshold l => GraphFieldMachine.instruction .threshold (fieldSlots slots false)
      (fun l => labels (.threshold l)) (some (labels (.endpoints .scan))) l
  | .endpoints l => GraphFieldMachine.instruction .endpoints (fieldSlots slots true)
      (fun l => labels (.endpoints l)) (some (labels (.vertices .scan))) l
  | .vertices l => GraphTokenMachine.instruction .vertex (tokenSlots slots false)
      (fun l => labels (.vertices l)) (some (labels (.edges .scan))) l
  | .edges l => GraphTokenMachine.instruction .edge (tokenSlots slots true)
      (fun l => labels (.edges l)) exit l

def preparedTapes (slots : Fin 7 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) : K → List Bool :=
  GraphTokenMachine.resultTapes .edge (tokenSlots slots true)
    (GraphTokenMachine.resultTapes .vertex (tokenSlots slots false)
      (GraphFieldMachine.resultTapes .endpoints (fieldSlots slots true)
        (GraphFieldMachine.resultTapes .threshold (fieldSlots slots false) base input)
        input) input) input

def steps (input : GraphReductionInput) : Nat :=
  GraphFieldMachine.steps .threshold input + GraphFieldMachine.steps .endpoints input +
    (3 * (graphBits input).length + 2) + (3 * (graphBits input).length + 2)

theorem preparedTapes_register (slots : Fin 7 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) (j : Fin 7) :
    preparedTapes slots base input (slots j) =
      match j.val with
      | 3 => GraphFieldMachine.fieldBits .threshold input ++ base (slots 3)
      | 4 => GraphFieldMachine.fieldBits .endpoints input ++ base (slots 4)
      | 5 => List.replicate input.graph.n true ++ base (slots 5)
      | 6 => List.replicate input.graph.edges.length true ++ base (slots 6)
      | _ => base (slots j) := by
  fin_cases j <;>
    simp [preparedTapes, GraphFieldMachine.resultTapes, GraphTokenMachine.resultTapes,
      GraphTokenMachine.tokenBits, GraphTokenMachine.count, slots.injective.eq_iff]

theorem preparedTapes_other (slots : Fin 7 ↪ K) (base : K → List Bool)
    (input : GraphReductionInput) (k : K)
    (h₃ : k ≠ slots 3) (h₄ : k ≠ slots 4) (h₅ : k ≠ slots 5) (h₆ : k ≠ slots 6) :
    preparedTapes slots base input k = base k := by
  simp [preparedTapes, GraphFieldMachine.resultTapes, GraphTokenMachine.resultTapes,
    h₃, h₄, h₅, h₆]

theorem steps_le (input : GraphReductionInput) :
    steps input ≤ 14 * (graphBits input).length + 10 := by
  have hk := GraphFieldMachine.steps_le .threshold input
  have he := GraphFieldMachine.steps_le .endpoints input
  unfold steps
  omega

end BinPackingGap.GraphPreparationMachine

namespace BinPackingGap.PackingMachineBlocks

open Turing
open BinPackingGames.Foundations.Complexity
open FiniteTapeProgram

inductive State
  | graph (state : GraphFieldMachine.State Unit)
  | arithmetic (state : BinaryAddMachine.State Unit)
  | emission (state : MachineFieldTemplate.State Unit)
  deriving DecidableEq, Fintype

def graphControl : MachineControlEmbedding.Control (GraphFieldMachine.State Unit) State where
  put := State.graph
  get
    | .graph s => s
    | _ => GraphFieldMachine.clean ()
  get_put _ := rfl

def arithmeticControl : MachineControlEmbedding.Control (BinaryAddMachine.State Unit) State where
  put := State.arithmetic
  get
    | .arithmetic s => s
    | _ => BinaryAddMachine.clean ()
  get_put _ := rfl

variable {K : Type} [DecidableEq K]

def invoke {σ L : Type} [Fintype L] (control : MachineControlEmbedding.Control σ State)
    (initial : σ) (main : L) (program : L → TM2.Stmt (fun _ : K => Bool) L σ) :
    Code (K := K) (S := State) :=
  .seq (.atom (.load (fun _ => control.put initial) .done))
    (.routine L inferInstance main
      (fun l => MachineControlEmbedding.statement control id none (program l)))

theorem invokeExec {σ L : Type} [Fintype L]
    (control : MachineControlEmbedding.Control σ State)
    (initial : σ) (main : L) (program : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (start : Data K State) (finishState : σ) (finishTapes : K → List Bool) (steps : Nat)
    (run : (MachineComposition.advance (TM2.step program))^[steps]
      (some ⟨some main, initial, start.tapes⟩) =
      some ⟨none, finishState, finishTapes⟩) :
    Exec (invoke control initial main program) start (1 + steps)
      ⟨control.put finishState, finishTapes⟩ := by
  refine Exec.seq (Exec.atom (.load (fun _ => control.put initial) .done) start) ?_
  apply Exec.routine inferInstance main
    (fun l => MachineControlEmbedding.statement control id none (program l))
  have translated := MachineControlEmbedding.trace control id none program
    (fun l => MachineControlEmbedding.statement control id none (program l))
    (fun _ => rfl) steps ⟨some main, initial, start.tapes⟩
    ⟨none, finishState, finishTapes⟩ run
  simpa only [Action.eval, MachineControlEmbedding.configuration,
    MachineSubroutine.label, id_eq] using translated

theorem invokeExecInTime {σ L : Type} [Fintype L]
    (control : MachineControlEmbedding.Control σ State)
    (initial : σ) (main : L) (program : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (start : Data K State) (finishState : σ) (finishTapes : K → List Bool) (budget : Nat)
    (run : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some main, initial, start.tapes⟩ (some ⟨none, finishState, finishTapes⟩) budget) :
    ∃ steps ≤ budget + 1, Exec (invoke control initial main program) start steps
      ⟨control.put finishState, finishTapes⟩ := by
  refine ⟨1 + run.steps, ?_, ?_⟩
  · have h := run.steps_le_m
    omega
  · exact invokeExec control initial main program start finishState finishTapes
      run.steps run.evals_in_steps

def prepareGraph (slots : Fin 7 ↪ K) : Code (K := K) (S := State) :=
  invoke graphControl (GraphFieldMachine.clean ()) (.threshold .scan)
    (GraphPreparationMachine.instruction slots id none)

theorem prepareGraph_cost (input : GraphReductionInput) :
    1 + GraphPreparationMachine.steps input ≤ 14 * (graphBits input).length + 11 := by
  have h := GraphPreparationMachine.steps_le input
  omega

end BinPackingGap.PackingMachineBlocks

namespace BinPackingGap.PackingArithmeticProgram

open FiniteTapeProgram PackingMachineBlocks

variable {K : Type} [DecidableEq K]

def code (body : Code (K := K) (S := BinaryAddMachine.State Unit)) :
    Code (K := K) (S := State) :=
  invoke arithmeticControl (BinaryAddMachine.clean ()) body.entry
    (body.instruction id none)

theorem exec (body : Code (K := K) (S := BinaryAddMachine.State Unit))
    (before after : K → List Bool) (steps : Nat) (state : State)
    (run : Exec body ⟨BinaryAddMachine.clean (), before⟩ steps
      ⟨BinaryAddMachine.clean (), after⟩) :
    Exec (code body) ⟨state, before⟩ (1 + steps)
      ⟨.arithmetic (BinaryAddMachine.clean ()), after⟩ := by
  exact invokeExec arithmeticControl (BinaryAddMachine.clean ()) body.entry
    (body.instruction id none) ⟨state, before⟩ (BinaryAddMachine.clean ()) after steps
    (run.trace (body.instruction id none) id none (fun _ => rfl))

theorem exec_in_time (body : Code (K := K) (S := BinaryAddMachine.State Unit))
    (before after : K → List Bool) (budget : Nat) (state : State)
    (run : ∃ steps ≤ budget, Exec body ⟨BinaryAddMachine.clean (), before⟩ steps
      ⟨BinaryAddMachine.clean (), after⟩) :
    ∃ steps ≤ budget + 1, Exec (code body) ⟨state, before⟩ steps
      ⟨.arithmetic (BinaryAddMachine.clean ()), after⟩ := by
  obtain ⟨steps, bound, actual⟩ := run
  exact ⟨1 + steps, by omega, exec body before after steps state actual⟩

end BinPackingGap.PackingArithmeticProgram

namespace BinPackingGap.PackingCountedProgram

open FiniteTapeProgram PackingMachineBlocks
open scoped BigOperators

variable {K : Type} [DecidableEq K]

def guardState (head : Option Bool) : State :=
  .arithmetic ((((), false), none), head)

def guard (counter : K) : Action K State :=
  .pop counter (fun _ head => guardState head) .done

def more : State → Bool
  | .arithmetic state => state.2.isSome
  | _ => false

def loop (counter : K) (body : Code (K := K) (S := State)) : Code (K := K) (S := State) :=
  .loop (guard counter) more body

theorem guard_succ (counter : K) (base : K → List Bool) (n : Nat) (state : State) :
    (guard counter).eval ⟨state, counterTapes counter base (n + 1)⟩ =
      ⟨guardState (some true), counterTapes counter base n⟩ := by
  simp [guard, Action.eval, counterTapes, List.replicate_succ]

theorem guard_zero (counter : K) (base : K → List Bool) (state : State) :
    (guard counter).eval ⟨state, counterTapes counter base 0⟩ =
      ⟨guardState none, counterTapes counter base 0⟩ := by
  simp [guard, Action.eval, counterTapes]

end BinPackingGap.PackingCountedProgram

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_PackingRegisterUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.PackingRegisterUpdate

open Turing
open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram
open FiniteTapeProgram PackingMachineBlocks

theorem operation_size_le (kind : Kind) (a b : Nat) :
    (operation kind a b).size ≤ a.size + b.size + 1 := by
  cases kind with
  | add =>
      have h := BinaryArithmetic.size_add_le a b
      change (a + b).size ≤ a.size + b.size + 1
      omega
  | multiply =>
      exact (BinaryArithmetic.size_mul_le a b).trans (Nat.le_succ _)

end BinPackingGap.PackingRegisterUpdate

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingVertexUpdate
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingMachineLayout

open NatExpressionCompiler PairExpressionCompiler BinaryRegisterProgram
open PackingRegisterFrame

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input]

variable [DecidableEq Other] [DecidableEq Extra]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
theorem item_shape (num : Descriptor → Expr Input) (den : Expr Input)
    (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (d : Descriptor) :
    registerTapes (itemSlots num den d) (tapes num den base input other)
      (initial (num d) den input) = tapes num den base input other := by
  classical
  rw [← values_itemRegisters num den input other d]
  exact restrict (registers num den) (itemRegisters num den d) base
    (values num den input other)

theorem values_update_input (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (a : Input) (n : Nat) :
    values num den (Function.update input a n) other =
      Function.update (values num den input other) (inputs num den a) n := by
  change values num den (Function.update input a n) other =
    Function.update (values num den input other) (.inl (.inl a)) n
  funext r
  cases r with
  | inl r =>
      cases r with
      | inl b => simp [values, Function.update_apply]
      | inr b => simp [values]
  | inr node => simp [values]

theorem values_update_other (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (a : Other) (n : Nat) :
    values num den input (Function.update other a n) =
      Function.update (values num den input other) (others num den a) n := by
  change values num den input (Function.update other a n) =
    Function.update (values num den input other) (.inl (.inr a)) n
  funext r
  cases r with
  | inl r =>
      cases r with
      | inl b => simp [values]
      | inr b => simp [values, Function.update_apply]
  | inr node => simp [values]

end BinPackingGap.PackingMachineLayout

namespace BinPackingGap.PackingLayoutCommands

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open PackingMachineLayout

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] in
theorem values_width (num : Descriptor → Expr Input) (den : Expr Input)
    (input : Input → Nat) (other : Other → Nat) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∀ r, (values num den input other r).size ≤ width := by
  intro r
  rcases r with (a | b) | node
  · exact hi a
  · exact ho b
  · simp [values]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] in
theorem input_ne_other (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (source : Other) :
    inputs num den destination ≠ others num den source := by
  change (Sum.inl (Sum.inl destination) : Reg num den Other) ≠ Sum.inl (Sum.inr source)
  simp

end BinPackingGap.PackingLayoutCommands

namespace BinPackingGap.PackingVertexUpdate

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input]

def updateSlots (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary) :
    (Fin 3 ⊕ Fin 6) ↪ PackingMachineLayout.Tape num den Other Extra :=
  PackingRegisterFrame.localSlots (PackingMachineLayout.registers num den)
    (updateRegisters num den power three temporary distinct)

omit [DecidableEq Descriptor] [DecidableEq Input] in
theorem values_updateRegisters (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary)
    (input : Input → Nat) (other : Other → Nat)
    (hthree : other three = 3) (htemporary : other temporary = 0) :
    PackingMachineLayout.values num den input other ∘
        updateRegisters num den power three temporary distinct =
      PackingRegisterUpdate.values 3 (input power) := by
  funext r
  fin_cases r <;>
    simp [PackingRegisterUpdate.values, hthree, htemporary]

variable [DecidableEq Other] [DecidableEq Extra]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
theorem shape (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat)
    (hthree : other three = 3) (htemporary : other temporary = 0) :
    registerTapes (updateSlots num den power three temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values 3 (input power)) =
      PackingMachineLayout.tapes num den base input other := by
  rw [← values_updateRegisters num den power three temporary distinct input other
    hthree htemporary]
  exact PackingRegisterFrame.restrict (PackingMachineLayout.registers num den)
    (updateRegisters num den power three temporary distinct) base
    (PackingMachineLayout.values num den input other)

omit [DecidableEq Extra] in
theorem updated_shape (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (three temporary : Other) (distinct : three ≠ temporary)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat)
    (hthree : other three = 3) (htemporary : other temporary = 0) :
    registerTapes (updateSlots num den power three temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values 3 (3 * input power)) =
      PackingMachineLayout.tapes num den base
        (Function.update input power (3 * input power)) other := by
  apply PackingRegisterFrame.replace (PackingMachineLayout.registers num den)
    (updateRegisters num den power three temporary distinct) base
    (PackingMachineLayout.values num den input other)
    (PackingMachineLayout.values num den (Function.update input power (3 * input power)) other)
    (PackingRegisterUpdate.values 3 (3 * input power))
  · intro r
    fin_cases r <;> simp [PackingRegisterUpdate.values, hthree, htemporary]
  · intro r hr
    have hrne : r ≠ PackingMachineLayout.inputs num den power := by
      intro heq
      apply hr
      refine ⟨1, ?_⟩
      simpa only [updateRegisters_one] using heq.symm
    simp only [PackingMachineLayout.values_update_input, Function.update_of_ne hrne]

omit [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra] in
theorem general_shape (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (baseRegister temporary : Other) (distinct : baseRegister ≠ temporary)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (htemporary : other temporary = 0) :
    registerTapes (updateSlots num den power baseRegister temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values (other baseRegister) (input power)) =
      PackingMachineLayout.tapes num den base input other := by
  have hvalues : PackingMachineLayout.values num den input other ∘
      updateRegisters num den power baseRegister temporary distinct =
        PackingRegisterUpdate.values (other baseRegister) (input power) := by
    funext r
    fin_cases r <;> simp [PackingRegisterUpdate.values, htemporary]
  rw [← hvalues]
  exact PackingRegisterFrame.restrict (PackingMachineLayout.registers num den)
    (updateRegisters num den power baseRegister temporary distinct) base
    (PackingMachineLayout.values num den input other)

omit [DecidableEq Extra] in
theorem general_updated_shape (num : Descriptor → Expr Input) (den : Expr Input)
    (power : Input) (baseRegister temporary : Other) (distinct : baseRegister ≠ temporary)
    (kind : PackingRegisterUpdate.Kind)
    (base : PackingMachineLayout.Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (htemporary : other temporary = 0) :
    registerTapes (updateSlots num den power baseRegister temporary distinct)
        (PackingMachineLayout.tapes num den base input other)
        (PackingRegisterUpdate.values (other baseRegister)
          (PackingRegisterUpdate.operation kind (other baseRegister) (input power))) =
      PackingMachineLayout.tapes num den base
        (Function.update input power
          (PackingRegisterUpdate.operation kind (other baseRegister) (input power))) other := by
  apply PackingRegisterFrame.replace (PackingMachineLayout.registers num den)
    (updateRegisters num den power baseRegister temporary distinct) base
    (PackingMachineLayout.values num den input other)
    (PackingMachineLayout.values num den
      (Function.update input power
        (PackingRegisterUpdate.operation kind (other baseRegister) (input power))) other)
    (PackingRegisterUpdate.values (other baseRegister)
      (PackingRegisterUpdate.operation kind (other baseRegister) (input power)))
  · intro r
    fin_cases r <;> simp [PackingRegisterUpdate.values, htemporary]
  · intro r hr
    have hrne : r ≠ PackingMachineLayout.inputs num den power := by
      intro heq
      apply hr
      refine ⟨1, ?_⟩
      simpa only [updateRegisters_one] using heq.symm
    simp only [PackingMachineLayout.values_update_input, Function.update_of_ne hrne]

end BinPackingGap.PackingVertexUpdate

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobLoop
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

namespace BinPackingGap.NatExpressionCompiler

variable {α β : Type}

theorem eval_substitute (replacement : α → Expr β) (values : β → Nat) (e : Expr α) :
    eval values (substitute replacement e) = eval (fun a => eval values (replacement a)) e := by
  induction e <;> simp_all [substitute, eval]

theorem eval_rename (f : α → β) (values : β → Nat) (e : Expr α) :
    eval values (rename f e) = eval (values ∘ f) e := by
  simpa only [rename, eval_input, Function.comp_def] using
    eval_substitute (fun a => .input (f a)) values e

end BinPackingGap.NatExpressionCompiler

namespace BinPackingGap.PackingItemExpression

open NatExpressionCompiler

def numerator (subclass : Subclass) (coordinate : PackingCoordinateExpression.Parts) :
    Expr Variable := substitute (scalarReplacement coordinate)
      (PackingScalarExpression.numerator subclass)

def values (D : InventoryData) (i : D.Item) : Variable → Nat
  | .vertexPower => 3 ^ D.graph.n
  | .geometry => D.coordinateDenominator
  | .labelPower => NaturalPackingNumerator.labelPower (D.itemLabel i)
  | .totalPower => PackingCoordinateExpression.coordinateValues D i .totalPowerA
  | .edgePower => PackingCoordinateExpression.coordinateValues D i .edgePower
  | .repetitionOne => PackingCoordinateExpression.coordinateValues D i .repetitionOne

end BinPackingGap.PackingItemExpression

end

namespace BinPackingGap.PackingItemBlockMachine

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler
open PairExpressionCompiler

variable {α K A : Type} [DecidableEq α] [DecidableEq K]

def record (num den : Expr α) (values : α → Nat) : List Bool :=
  true :: (BinaryEncoding.natBits (eval values num) ++ BinaryEncoding.natBits (eval values den))

theorem consumed_width (num den : Expr α) (values : Reg num den → Nat) (width : Nat)
    (h : ∀ r, (values r).size ≤ width) :
    ∀ r, (consumed num den values r).size ≤ width := by
  intro r
  by_cases hd : r = denRoot num den
  · subst r; simp [consumed]
  · by_cases hn : r = numRoot num den
    · subst r; simp [consumed, hd]
    · simpa [consumed, hd, hn] using h r

end BinPackingGap.PackingItemBlockMachine

namespace BinPackingGap.PackingChunkMachine

open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler
open PairExpressionCompiler
open PackingItemBlockMachine (outputTapes)

variable {α δ K A : Type} [DecidableEq α] [DecidableEq K]

def records (numerator : δ → Expr α) (denominator : Expr α)
    (values : δ → α → Nat) (descriptors : List δ) : List Bool :=
  descriptors.flatMap (fun d => PackingItemBlockMachine.record
    (numerator d) denominator (values d))

omit [DecidableEq α] in
@[simp] theorem records_nil (numerator : δ → Expr α) (denominator : Expr α)
    (values : δ → α → Nat) : records numerator denominator values [] = [] := rfl

omit [DecidableEq α] in
@[simp] theorem records_cons (numerator : δ → Expr α) (denominator : Expr α)
    (values : δ → α → Nat) (d : δ) (rest : List δ) :
    records numerator denominator values (d :: rest) =
      PackingItemBlockMachine.record (numerator d) denominator (values d) ++
        records numerator denominator values rest := by
  simp only [records, List.flatMap_cons]

@[simp] theorem outputTapes_nil (output : K) (base : K → List Bool) :
    outputTapes output base [] = base := by
  simp [outputTapes]

theorem outputTapes_append (output : K) (base : K → List Bool) (first second : List Bool) :
    outputTapes output (outputTapes output base first) second =
      outputTapes output base (first ++ second) := by
  simp only [outputTapes, Function.update_self, Function.update_idem,
    List.reverse_append, List.append_assoc]

theorem shape_after_output {R : Type} (slot : (R ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ i, slot i ≠ output) (base : K → List Bool)
    (values : R → Nat) (shape : registerTapes slot base values = base) (word : List Bool) :
    registerTapes slot (outputTapes output base word) values =
      outputTapes output base word := by
  classical
  unfold outputTapes
  rw [RegisterFrameEmission.external_update slot base values output outside, shape]

@[simp] theorem final_output (output : K) (base : K → List Bool) (word : List Bool) :
    outputTapes output base word output = word.reverse ++ base output := by
  simp [outputTapes]

end BinPackingGap.PackingChunkMachine

namespace BinPackingGap.PackingDescriptorExpression

open NatExpressionCompiler PackingInventoryDescriptors

def instantiate (fixed : InventoryData) (graph : GraphInput) (R k : Nat) : InventoryData :=
  { fixed with graph := graph, R := R, k := k }

@[simp] theorem vertexDescriptors_instantiate (fixed : InventoryData)
    (graph : GraphInput) (R k : Nat) :
    vertexDescriptors (instantiate fixed graph R k) = vertexDescriptors fixed := by
  have htree : (instantiate fixed graph R k).treeRowList = fixed.treeRowList := by
    rfl
  have hpositive : (instantiate fixed graph R k).positiveLocalList =
      fixed.positiveLocalList := by
    unfold InventoryData.positiveLocalList
    apply congrArg Finset.toList
    ext r
    constructor <;> intro _ <;> exact Finset.mem_univ _
  have hsubclass : (instantiate fixed graph R k).treeSubclass = fixed.treeSubclass := by
    funext r
    rcases r with p | (m | pad) <;> rfl
  have htreeDescriptor :
      PackingCoordinateExpression.treeDescriptor (instantiate fixed graph R k) =
        PackingCoordinateExpression.treeDescriptor fixed := by
    funext r
    rcases r with ⟨node, copy⟩ | (⟨node, copy⟩ | copy) <;> rfl
  have hlocal : positiveDescriptor (instantiate fixed graph R k) =
      positiveDescriptor fixed := by
    funext r
    apply Prod.ext rfl
    apply congrArg PackingCoordinateExpression.Descriptor.localDepth
    apply Fin.ext
    rfl
  simp only [vertexDescriptors, htree, hpositive, hsubclass, htreeDescriptor, hlocal]
  rfl

@[simp] theorem jobDescriptors_instantiate (fixed : InventoryData)
    (graph : GraphInput) (R k : Nat) :
    jobDescriptors (instantiate fixed graph R k) = jobDescriptors fixed := rfl

def numerator (D : InventoryData) (descriptor : ItemDescriptor D) :
    Expr PackingItemExpression.Variable :=
  PackingItemExpression.numerator descriptor.1
    (PackingCoordinateExpression.expression D.geometryBound descriptor.2)

@[simp] theorem numerator_instantiate (fixed : InventoryData)
    (graph : GraphInput) (R k : Nat) (descriptor : ItemDescriptor fixed) :
    numerator (instantiate fixed graph R k) descriptor = numerator fixed descriptor := rfl

def values (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat) :
    PackingItemExpression.Variable → Nat
  | .vertexPower => 3 ^ D.graph.n
  | .geometry => D.coordinateDenominator
  | .labelPower => NaturalPackingNumerator.labelPower label
  | .totalPower => (D.R + 1) ^ D.graph.edges.length
  | .edgePower => (D.R + 1) ^ edge
  | .repetitionOne => rep

theorem coordinate_values (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat) :
    values D label edge rep ∘ PackingItemExpression.coordinateVariable =
      PackingCoordinateExpression.registers D edge rep := by
  funext v
  cases v <;> rfl

theorem replacement_values (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat)
    (descriptor : ItemDescriptor D) :
    (fun v => eval (values D label edge rep)
      (PackingItemExpression.scalarReplacement
        (PackingCoordinateExpression.expression D.geometryBound descriptor.2) v)) =
      PackingScalarExpression.values D.coordinateDenominator label
        ((PackingCoordinateExpression.expression D.geometryBound descriptor.2).eval
          (PackingCoordinateExpression.registers D edge rep)) := by
  funext v
  cases v with
  | vertexPower => rfl
  | geometry => rfl
  | labelPower => rfl
  | coordinatePositive =>
      simp only [PackingItemExpression.scalarReplacement, eval_rename, coordinate_values]
      rfl
  | coordinateNegative =>
      simp only [PackingItemExpression.scalarReplacement, eval_rename, coordinate_values]
      rfl

theorem eval_numerator (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat)
    (descriptor : ItemDescriptor D) :
    eval (values D label edge rep) (numerator D descriptor) =
      (rawOfDescriptor D label edge rep descriptor).1 := by
  rw [numerator, PackingItemExpression.numerator, eval_substitute, replacement_values,
    PackingScalarExpression.eval_numerator]
  rfl

theorem eval_denominator (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat) :
    eval (values D label edge rep) PackingItemExpression.denominator =
      IntegerPackingArithmetic.sizeDenominator D.graph.n D.coordinateDenominator := rfl

def rawRecord (pair : Nat × Nat) : List Bool :=
  true :: (BinaryEncoding.natBits pair.1 ++ BinaryEncoding.natBits pair.2)

theorem record_eq (D : InventoryData) (label : Option D.Vertex) (edge rep : Nat)
    (descriptor : ItemDescriptor D) :
    PackingItemBlockMachine.record (numerator D descriptor) PackingItemExpression.denominator
      (values D label edge rep) = rawRecord (rawOfDescriptor D label edge rep descriptor) := by
  simp only [PackingItemBlockMachine.record, eval_numerator, eval_denominator,
    rawRecord, rawOfDescriptor]

end BinPackingGap.PackingDescriptorExpression

namespace BinPackingGap.PackingVertexLoop

open NatExpressionCompiler

variable {α δ : Type} [DecidableEq α]

@[simp] theorem vertexInput_power (input : α → Nat) (power : α) (v : Nat) :
    vertexInput input power v power = 3 ^ (v + 1) := by
  simp [vertexInput]

theorem vertexInput_other (input : α → Nat) (power : α) (v : Nat)
    (a : α) (different : a ≠ power) : vertexInput input power v a = input a := by
  simp [vertexInput, different]

theorem vertexInput_update (input : α → Nat) (power : α) (v : Nat) :
    Function.update (vertexInput input power v) power
      (3 * vertexInput input power v power) = vertexInput input power (v + 1) := by
  have powerStep : 3 * 3 ^ (v + 1) = 3 ^ ((v + 1) + 1) :=
    (Nat.mul_comm 3 (3 ^ (v + 1))).trans (Nat.pow_succ 3 (v + 1)).symm
  rw [vertexInput_power]
  unfold vertexInput
  rw [Function.update_idem, powerStep]

theorem pow3_size_le (n : Nat) : (3 ^ n).size ≤ 2 * n + 1 := by
  have bound := BinaryArithmetic.size_pow_le 3 n
  have sizeThree : (3 : Nat).size = 2 := by decide
  rw [sizeThree, Nat.mul_comm n 2] at bound
  exact bound

theorem vertexInput_size_le (input : α → Nat) (power : α)
    (inputWidth start count v : Nat)
    (initial : ∀ a, (input a).size ≤ inputWidth) (hv : v ≤ start + count) :
    ∀ a, (vertexInput input power v a).size ≤ aggregateWidth inputWidth start count := by
  intro a
  by_cases same : a = power
  · subst a
    rw [vertexInput_power]
    have bound := pow3_size_le (v + 1)
    unfold aggregateWidth
    omega
  · rw [vertexInput_other input power v a same]
    have bound := initial a
    unfold aggregateWidth
    omega

def stream (numerator : δ → Expr α) (denominator : Expr α) (descriptors : List δ)
    (input : α → Nat) (power : α) (start : Nat) : Nat → List Bool
  | 0 => []
  | count + 1 =>
      PackingChunkMachine.records numerator denominator
        (fun _ => vertexInput input power start) descriptors ++
      stream numerator denominator descriptors input power (start + 1) count

@[simp] theorem stream_zero (numerator : δ → Expr α) (denominator : Expr α)
    (descriptors : List δ) (input : α → Nat) (power : α) (start : Nat) :
    stream numerator denominator descriptors input power start 0 = [] := rfl

@[simp] theorem stream_succ (numerator : δ → Expr α) (denominator : Expr α)
    (descriptors : List δ) (input : α → Nat) (power : α) (start count : Nat) :
    stream numerator denominator descriptors input power start (count + 1) =
      PackingChunkMachine.records numerator denominator
        (fun _ => vertexInput input power start) descriptors ++
      stream numerator denominator descriptors input power (start + 1) count := rfl

end BinPackingGap.PackingVertexLoop

namespace BinPackingGap.PackingJobBody

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

@[simp] theorem nextInput_repetition (input : α → Nat) (power repetition : α)
    (rightValue : Nat) :
    nextInput input power repetition rightValue repetition = input repetition + 1 := by
  simp [nextInput]

@[simp] theorem nextInput_power (input : α → Nat) (power repetition : α)
    (different : power ≠ repetition) (rightValue : Nat) :
    nextInput input power repetition rightValue power = rightValue := by
  simp [nextInput, different]

def pairRecords (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (input : α → Nat) (power : α) (leftValue rightValue : Nat) : List Bool :=
  PackingChunkMachine.records num den
      (fun _ => Function.update input power leftValue) descriptors ++
    PackingChunkMachine.records num den
      (fun _ => Function.update input power rightValue) descriptors

theorem layout_external_update (num : δ → Expr α) (den : Expr α)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (external : Extra) (word : List Bool) :
    tapes num den (Function.update base (.inr external) word) input other =
      Function.update (tapes num den base input other) (.inr external) word := by
  apply RegisterFrameEmission.external_update
  intro i
  simp [registers]

theorem layout_output (num : δ → Expr α) (den : Expr α)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (output : Extra) (word : List Bool) :
    outputTapes (.inr output) (tapes num den base input other) word =
      tapes num den (outputTapes (.inr output) base word) input other := by
  unfold outputTapes
  rw [tapes_extra, layout_external_update]

end BinPackingGap.PackingJobBody

namespace BinPackingGap.PackingVertexRecords

open NatExpressionCompiler

theorem stream_eq_finRange {α δ : Type} [DecidableEq α]
    (numerator : δ → Expr α) (denominator : Expr α) (descriptors : List δ)
    (input : α → Nat) (power : α) (start count : Nat) :
    PackingVertexLoop.stream numerator denominator descriptors input power start count =
      (List.finRange count).flatMap (fun i =>
        PackingChunkMachine.records numerator denominator
          (fun _ => PackingVertexLoop.vertexInput input power (start + i.val)) descriptors) := by
  induction count generalizing start with
  | zero => simp [PackingVertexLoop.stream]
  | succ count ih =>
      simp only [PackingVertexLoop.stream_succ, finRange_cons, List.flatMap_cons,
        List.flatMap_map, Fin.val_zero, Fin.val_succ, Nat.add_zero, ih]
      congr 1
      apply List.flatMap_congr
      intro i _
      have index : start + 1 + i.val = start + (i.val + 1) := by omega
      rw [index]

theorem values_vertexInput (D : InventoryData) (v : D.Vertex) :
    PackingVertexLoop.vertexInput (PackingDescriptorExpression.values D none 0 0)
        .labelPower v.val =
      PackingDescriptorExpression.values D (some v) 0 0 := by
  funext coordinate
  cases coordinate <;>
    simp [PackingVertexLoop.vertexInput, PackingDescriptorExpression.values,
      NaturalPackingNumerator.labelPower]

end BinPackingGap.PackingVertexRecords

namespace BinPackingGap.PackingJobLoop

section

open NatExpressionCompiler

variable {α δ : Type} [DecidableEq α]

def iterationInput (input : α → Nat) (power repetition : α) (right : Nat) :
    Nat → α → Nat
  | 0 => input
  | n + 1 => Function.update (Function.update input power right) repetition
      (input repetition + (n + 1))

@[simp] theorem iterationInput_zero (input : α → Nat) (power repetition : α) (right : Nat) :
    iterationInput input power repetition right 0 = input := rfl

@[simp] theorem iterationInput_rep (input : α → Nat) (power repetition : α)
    (right n : Nat) :
    iterationInput input power repetition right n repetition = input repetition + n := by
  cases n <;> simp [iterationInput]

theorem iterationInput_power (input : α → Nat) (power repetition : α) (right : Nat)
    (distinct : power ≠ repetition) (n : Nat) (positive : 0 < n) :
    iterationInput input power repetition right n power = right := by
  cases n with
  | zero => omega
  | succ n => simp [iterationInput, distinct]

theorem iterationInput_other (input : α → Nat) (power repetition : α)
    (right n : Nat) (a : α) (notPower : a ≠ power) (notRepetition : a ≠ repetition) :
    iterationInput input power repetition right n a = input a := by
  cases n <;> simp [iterationInput, notPower, notRepetition]

theorem iterationInput_succ (input : α → Nat) (power repetition : α) (right : Nat)
    (distinct : power ≠ repetition) (n : Nat) :
    iterationInput (PackingJobBody.nextInput input power repetition right)
        power repetition right n =
      iterationInput input power repetition right (n + 1) := by
  cases n with
  | zero => rfl
  | succ n =>
      funext a
      by_cases atRepetition : a = repetition
      · subst a
        simp [iterationInput, PackingJobBody.nextInput,
          Nat.add_comm, Nat.add_left_comm]
      · by_cases atPower : a = power
        · subst a
          simp [iterationInput, PackingJobBody.nextInput, distinct]
        · simp [iterationInput, PackingJobBody.nextInput, atRepetition, atPower]

theorem size_le_succ (n : Nat) : n.size ≤ n + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have bound := BinaryArithmetic.size_add_le n 1
      have sizeOne : (1 : Nat).size = 1 := by decide
      rw [sizeOne] at bound
      omega

theorem iterationInput_size_le (input : α → Nat) (power repetition : α) (right : Nat)
    (distinct : power ≠ repetition) (inputWidth otherWidth count n : Nat)
    (within : n ≤ count) (initial : ∀ a, (input a).size ≤ inputWidth)
    (rightBound : right.size ≤ otherWidth) :
    ∀ a, (iterationInput input power repetition right n a).size ≤
      aggregateWidth inputWidth otherWidth count := by
  intro a
  by_cases atRepetition : a = repetition
  · subst a
    rw [iterationInput_rep]
    have bound := BinaryArithmetic.size_add_le (input repetition) n
    have sizeN := size_le_succ n
    have sizeInitial := initial repetition
    unfold aggregateWidth
    omega
  · cases n with
    | zero =>
        simp only [iterationInput_zero]
        have bound := initial a
        unfold aggregateWidth
        omega
    | succ n =>
        by_cases atPower : a = power
        · subst a
          rw [iterationInput_power input power repetition right distinct (n + 1)
            (Nat.succ_pos n)]
          unfold aggregateWidth
          omega
        · rw [iterationInput_other input power repetition right (n + 1) a
            atPower atRepetition]
          have bound := initial a
          unfold aggregateWidth
          omega

def stream (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (input : α → Nat) (power repetition : α) (left right : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => PackingJobBody.pairRecords num den descriptors input power left right ++
      stream num den descriptors (PackingJobBody.nextInput input power repetition right)
        power repetition left right n

@[simp] theorem stream_zero (num : δ → Expr α) (den : Expr α)
    (descriptors : List δ) (input : α → Nat) (power repetition : α) (left right : Nat) :
    stream num den descriptors input power repetition left right 0 = [] := rfl

@[simp] theorem stream_succ (num : δ → Expr α) (den : Expr α)
    (descriptors : List δ) (input : α → Nat) (power repetition : α) (left right n : Nat) :
    stream num den descriptors input power repetition left right (n + 1) =
      PackingJobBody.pairRecords num den descriptors input power left right ++
        stream num den descriptors (PackingJobBody.nextInput input power repetition right)
          power repetition left right n := rfl

end

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open PackingJobBody (nextInput pairRecords )

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

theorem layout_counter (num : δ → Expr α) (den : Expr α)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (counter : Extra) (n : Nat) :
    tapes num den (counterTapes (.inr counter) base n) input other =
      counterTapes (.inr counter) (tapes num den base input other) n := by
  apply RegisterFrameEmission.external_update
  intro i
  simp [registers]

theorem output_counter (num : δ → Expr α) (den : Expr α)
    (base : Tape num den Other Extra → List Bool) (output counter : Extra)
    (different : output ≠ counter) (word : List Bool) (n : Nat) :
    outputTapes (.inr output) (counterTapes (.inr counter) base n) word =
      counterTapes (.inr counter) (outputTapes (.inr output) base word) n := by
  funext k
  by_cases ho : k = .inr output
  · subst k
    simp [outputTapes, counterTapes, different]
  · by_cases hc : k = .inr counter
    · subst k
      simp [outputTapes, counterTapes, different, Ne.symm different]
    · simp [outputTapes, counterTapes, ho, hc]

end BinPackingGap.PackingJobLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingSetupGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingSetupExpression

def inventoryOutput (D : InventoryData) : Output → Nat
  | .repetitions => D.R
  | .base => D.R + 1
  | .edgeRepetitions => D.graph.edges.length * D.R
  | .bins => D.B
  | .upOne => D.globalStock (.up true)
  | .upZero => D.globalStock (.up false)
  | .umOne => D.globalStock (.um true)
  | .umZero => D.globalStock (.um false)
  | .edgeStock => D.d * D.R
  | .treeFlags => D.flagStock .tree
  | .jobFlags => D.flagStock .main
  | .one => 1
  | .three => 3

theorem outputValues_eq_inventory (p : Parameters) (D : InventoryData)
    (hd : p.d = D.d) (hplus : p.tPlus = D.tPlus) (hminus : p.tMinus = D.tMinus)
    (hR : D.R = 100 * (p.P + D.graph.n * p.K + 1)) :
    outputValues p D.graph.n D.graph.edges.length D.k = inventoryOutput D := by
  funext o
  cases o <;>
    simp [outputValues, inventoryOutput, ← hR, hd, hplus, hminus,
      InventoryData.globalStock, InventoryData.flagStock, InventoryData.minusSlots,
      InventoryData.treeFlags, InventoryData.jobFlags, D.B_closed, D.plusSlots_eq,
      D.sum_J, InventoryData.t, Nat.mul_assoc]

end BinPackingGap.PackingSetupExpression

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_GraphPackingRegisters
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingRegisters

open PackingItemExpression PackingInventoryDescriptors
open PackingMachineLayout PackingRegisterFrame

def parameters (fixed : InventoryData) (K : Nat) : PackingSetupExpression.Parameters :=
  ⟨fixed.P, K, fixed.d, fixed.tPlus, fixed.tMinus⟩

abbrev Numerator (fixed : InventoryData) := PackingDescriptorExpression.numerator fixed
abbrev Other (fixed : InventoryData) (K : Nat) := PackingSetupMachine.Reg (parameters fixed K) ⊕ Work
abbrev Register (fixed : InventoryData) (K : Nat) :=
  PackingMachineLayout.Reg (Numerator fixed) denominator (Other fixed K)
abbrev Tape (fixed : InventoryData) (K : Nat) :=
  PackingMachineLayout.Tape (Numerator fixed) denominator (Other fixed K) Extra

def slots (fixed : InventoryData) (K : Nat) :
    (Register fixed K ⊕ Fin 6) ↪ Tape fixed K := registers (Numerator fixed) denominator

def item (fixed : InventoryData) (K : Nat) : Variable ↪ Register fixed K :=
  inputs (Numerator fixed) denominator

def setup (fixed : InventoryData) (K : Nat) :
    PackingSetupMachine.Reg (parameters fixed K) ↪ Register fixed K :=
  (Function.Embedding.inl : PackingSetupMachine.Reg (parameters fixed K) ↪ Other fixed K).trans
    (others (Numerator fixed) denominator)

def work (fixed : InventoryData) (K : Nat) : Work ↪ Register fixed K :=
  (Function.Embedding.inr : Work ↪ Other fixed K).trans
    (others (Numerator fixed) denominator)

def input (fixed : InventoryData) (K : Nat) (i : PackingSetupExpression.Input) : Register fixed K :=
  setup fixed K (PackingSetupMachine.input (parameters fixed K) i)

def output (fixed : InventoryData) (K : Nat) (o : PackingSetupExpression.Output) : Register fixed K :=
  setup fixed K (PackingSetupMachine.output (parameters fixed K) o)

def setupSlots (fixed : InventoryData) (K : Nat) :
    (PackingSetupMachine.Reg (parameters fixed K) ⊕ Fin 6) ↪ Tape fixed K :=
  localSlots (slots fixed K) (setup fixed K)

def graphSlots (fixed : InventoryData) (K : Nat) : Fin 7 ↪ Tape fixed K where
  toFun := ![.inr .input, .inr .scanScratch, .inr .scanTemporary,
    .inr .threshold, .inr .endpoints, .inr .vertices, .inr .edges]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def countRegister (fixed : InventoryData) (K : Nat) : CountSource → Register fixed K
  | .input i => input fixed K i
  | .output o => output fixed K o
  | .endpoint right => work fixed K (if right then .rightEndpoint else .leftEndpoint)

def tallyRegisters (fixed : InventoryData) (K : Nat) (source : CountSource) :
    BinaryToTallyMachine.Reg ↪ Register fixed K where
  toFun
    | .source => countRegister fixed K source
    | .counter => work fixed K .counter
    | .one => work fixed K .one
    | .temporary => work fixed K .temporary
  inj' := by
    intro a b h
    cases source with
    | input i =>
        cases a <;> cases b <;>
          simp_all [countRegister, input, setup, work, others, PackingSetupMachine.input]
    | output o =>
        cases a <;> cases b <;>
          simp_all [countRegister, output, setup, work, others, PackingSetupMachine.output]
    | endpoint right =>
        cases right <;> cases a <;> cases b <;>
          simp_all [countRegister, work, others]

def tallySlots (fixed : InventoryData) (K : Nat) (source : CountSource) :
    (BinaryToTallyMachine.Reg ⊕ Fin 6) ↪ Tape fixed K :=
  localSlots (slots fixed K) (tallyRegisters fixed K source)

theorem tally_outside (fixed : InventoryData) (K : Nat) (source : CountSource)
    (tape : Extra) (i : BinaryToTallyMachine.Reg ⊕ Fin 6) :
    tallySlots fixed K source i ≠ Sum.inr tape := by
  simp [tallySlots, localSlots, slots, registers]

def endpointRegisters (fixed : InventoryData) (K : Nat) (right : Bool) :
    Fin 7 ↪ Register fixed K where
  toFun := ![countRegister fixed K (.endpoint right), output fixed K .three,
    work fixed K (if right then .rightPower else .leftPower), work fixed K .counter,
    work fixed K .one, work fixed K .temporary, work fixed K .reverse]
  inj' := by
    intro i j h
    cases right <;> fin_cases i <;> fin_cases j <;>
      simp_all [countRegister, output, setup, work, others, PackingSetupMachine.output]

def endpointSlots (fixed : InventoryData) (K : Nat) (right : Bool) :
    (Fin 7 ⊕ Fin 6) ↪ Tape fixed K :=
  localSlots (slots fixed K) (endpointRegisters fixed K right)

theorem endpoint_outside (fixed : InventoryData) (K : Nat) (right : Bool)
    (tape : Extra) (i : Fin 7 ⊕ Fin 6) :
    endpointSlots fixed K right i ≠ Sum.inr tape := by
  simp [endpointSlots, localSlots, slots, registers]

def powerSlots (fixed : InventoryData) (K : Nat) (source : CountSource)
    (destination : Variable) : Fin 11 ↪ Tape fixed K where
  toFun := ![slots fixed K (.inl (countRegister fixed K source)),
    slots fixed K (.inl (item fixed K destination)),
    slots fixed K (.inl (work fixed K .temporary)),
    slots fixed K (.inr 0), slots fixed K (.inr 1), slots fixed K (.inr 2),
    slots fixed K (.inr 3), slots fixed K (.inr 4), slots fixed K (.inr 5),
    .inr .powerCounter, slots fixed K (.inl (work fixed K .reverse))]
  inj' := by
    intro i j h
    cases source with
    | input a =>
        fin_cases i <;> fin_cases j <;>
          simp_all [countRegister, input, setup, work, item, inputs, others,
            slots, registers, PackingSetupMachine.input]
        all_goals
          first
          | change (Sum.inl (Sum.inr _) : Register fixed K) = Sum.inl (Sum.inl _) at h
          | change (Sum.inl (Sum.inl _) : Register fixed K) = Sum.inl (Sum.inr _) at h
          simp at h
    | output a =>
        fin_cases i <;> fin_cases j <;>
          simp_all [countRegister, output, setup, work, item, inputs, others,
            slots, registers, PackingSetupMachine.output]
        all_goals
          first
          | change (Sum.inl (Sum.inr _) : Register fixed K) = Sum.inl (Sum.inl _) at h
          | change (Sum.inl (Sum.inl _) : Register fixed K) = Sum.inl (Sum.inr _) at h
          simp at h
    | endpoint right =>
        cases right <;> fin_cases i <;> fin_cases j <;>
          simp_all [countRegister, work, item, inputs, others, slots, registers]
        all_goals
          first
          | change (Sum.inl (Sum.inr _) : Register fixed K) = Sum.inl (Sum.inl _) at h
          | change (Sum.inl (Sum.inl _) : Register fixed K) = Sum.inl (Sum.inr _) at h
          simp at h

def decoderSlots (fixed : InventoryData) (K : Nat) (right : Bool) : Fin 3 ↪ Tape fixed K where
  toFun := ![.inr .endpoints, .inr .decodeScratch,
    slots fixed K (.inl (countRegister fixed K (.endpoint right)))]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slots, registers]

def thresholdSlots (fixed : InventoryData) (K : Nat) : Fin 3 ↪ Tape fixed K where
  toFun := ![.inr .threshold, .inr .decodeScratch, slots fixed K (.inl (input fixed K .k))]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [slots, registers]

end BinPackingGap.GraphPackingRegisters

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_IntegralSpeciesCounts
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.decidableAncestor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem um_indicator_add (g : GlobalSpecies D.graph) :
    (if g = .um true then 1 else 0) + (if g = .um false then 1 else 0) =
      match g with | .um _ => 1 | _ => 0 := by
  cases g with
  | up b => rfl
  | um b => cases b <;> rfl
  | edge e b => rfl

theorem stateGlobalSpecies_um_true_count (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .um true)).card =
        if selected then 0 else D.d := by
  classical
  cases selected <;>
    simp [-Finset.sum_boole, Finset.card_filter, LocalBin, MBase, TreeRow,
      Fintype.sum_sum_type, Fintype.sum_prod_type, stateGlobalSpecies,
      stateMainGlobalSpecies]
  exact root_copy_indicator_sum D.minus D.d

theorem stateGlobalSpecies_um_total (v : D.Vertex) (selected : Bool) :
    (Finset.univ.filter (fun b : D.LocalBin v =>
      D.stateGlobalSpecies selected b = .um true)).card +
      (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies selected b = .um false)).card = D.tMinus := by
  classical
  simp only [Finset.card_filter, ← Finset.sum_add_distrib, D.um_indicator_add]
  simp [LocalBin, MBase, TreeRow, Fintype.sum_sum_type,
    stateGlobalSpecies, stateMainGlobalSpecies, tMinus, Nat.mul_comm]

theorem stateFlagSpecies_count (v : D.Vertex) (f : FlagSpecies) :
    (Finset.univ.filter (fun b : D.LocalBin v => D.stateFlagSpecies b = f)).card =
      match f with | .tree => D.t | .main => D.J v | .edge => D.J v := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sum_type]
  cases f <;> simp [stateFlagSpecies, D.card_jobCopy, t, tPlus, tMinus,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end BinPackingGap.InventoryData

namespace BinPackingGap

namespace InventoryData

variable (D : InventoryData)

def coverSelected (C : Finset D.Vertex) (v : D.Vertex) : Bool := decide (v ∈ C)

def permitLeft (C : Finset D.Vertex) (e : D.Edge) : Bool :=
  !D.coverSelected C (D.graph.left e) || D.coverSelected C (D.graph.right e)

def integralPermit (C : Finset D.Vertex) (e : D.Edge) (slot : Fin 2) : Bool :=
  if slot = 0 then D.permitLeft C e else !D.permitLeft C e

@[simp] theorem integralPermit_zero (C : Finset D.Vertex) (e : D.Edge) :
    D.integralPermit C e 0 = D.permitLeft C e := by simp [integralPermit]

@[simp] theorem integralPermit_one (C : Finset D.Vertex) (e : D.Edge) :
    D.integralPermit C e 1 = !D.permitLeft C e := by simp [integralPermit]

def integralGlobalSpecies (C : Finset D.Vertex) : D.PhysicalBins → GlobalSpecies D.graph
  | ⟨v, .inl b⟩ => D.stateMainGlobalSpecies (D.coverSelected C v) b
  | ⟨_, .inr j⟩ => .edge j.1.1.val.1 (D.integralPermit C j.1.1.val.1 j.1.1.val.2)

def integralFlagSpecies : D.PhysicalBins → FlagSpecies :=
  fun b => D.stateFlagSpecies b.2

end InventoryData

end BinPackingGap

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem integral_um_count_eq_sum (C : Finset D.Vertex) (one : Bool) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um one)).card =
      ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
        D.stateGlobalSpecies (D.coverSelected C v) b = .um one)).card := by
  classical
  simp only [Finset.card_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro b _
  rcases b with b | j
  · rfl
  · simp [integralGlobalSpecies, stateGlobalSpecies]

theorem integral_um_total (C : Finset D.Vertex) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralGlobalSpecies C b = .um true)).card +
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralGlobalSpecies C b = .um false)).card = D.minusSlots := by
  rw [D.integral_um_count_eq_sum, D.integral_um_count_eq_sum,
    ← Finset.sum_add_distrib]
  simp_rw [D.stateGlobalSpecies_um_total]
  simp [minusSlots]

theorem card_integralEdgeJobs (C : Finset D.Vertex) (e : D.Edge) (permit : Bool) :
    (Finset.univ.filter (fun j : Σ v : D.Vertex, D.JobCopy v =>
      GlobalSpecies.edge (G := D.graph) j.2.1.1.val.1
        (D.integralPermit C j.2.1.1.val.1 j.2.1.1.val.2) =
      GlobalSpecies.edge e permit)).card = D.d * D.R := by
  classical
  let chosen : Fin 2 := if permit = D.permitLeft C e then 0 else 1
  have hslot (slot : Fin 2) :
      D.integralPermit C e slot = permit ↔ slot = chosen := by
    have hs : slot = 0 ∨ slot = 1 := by omega
    rcases hs with rfl | rfl <;>
      cases hp : D.permitLeft C e <;> cases permit <;>
      simp [chosen, hp]
  have hedge (e' : D.Edge) (slot : Fin 2) :
      GlobalSpecies.edge (G := D.graph) e' (D.integralPermit C e' slot) =
        GlobalSpecies.edge e permit ↔ (e', slot) = (e, chosen) := by
    rw [GlobalSpecies.edge.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨he, hp⟩
      subst e'
      exact ⟨rfl, (hslot slot).mp hp⟩
    · rintro ⟨he, hs⟩
      subst e'
      exact ⟨rfl, (hslot slot).mpr hs⟩
  calc
    _ = ((({(e, chosen)} : Finset (D.Edge × Fin 2)) ×ˢ
          (Finset.univ : Finset (Fin D.R))) ×ˢ
          (Finset.univ : Finset (Fin D.d))).card := by
      apply Finset.card_equiv D.allJobEquiv
      intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, and_true]
      exact hedge j.2.1.1.val.1 j.2.1.1.val.2
    _ = D.d * D.R := by simp [Nat.mul_comm]

theorem card_integralFlagSpecies (f : FlagSpecies) :
    (Finset.univ.filter (fun b : D.PhysicalBins =>
      D.integralFlagSpecies b = f)).card = D.flagStock f := by
  classical
  have hsum :
      (Finset.univ.filter (fun b : D.PhysicalBins =>
        D.integralFlagSpecies b = f)).card =
        ∑ v : D.Vertex, (Finset.univ.filter (fun b : D.LocalBin v =>
          D.stateFlagSpecies b = f)).card := by
    rw [Finset.card_filter]
    simp only [Finset.card_filter, Fintype.sum_sigma, integralFlagSpecies]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro b _
    rfl
  rw [hsum]
  cases f <;> simp [D.stateFlagSpecies_count, flagStock, treeFlags, jobFlags]

end BinPackingGap.InventoryData

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Inventory_PackingConstantPool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingConstantPool

open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler PairExpressionCompiler
open PackingMachineBlocks
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable {α δ K : Type} [DecidableEq α] [DecidableEq K]

theorem output_counter_comm (output counter : K) (different : counter ≠ output)
    (base : K → List Bool) (n : Nat) (word : List Bool) :
    outputTapes output (counterTapes counter base n) word =
      counterTapes counter (outputTapes output base word) n := by
  funext k
  by_cases ho : k = output
  · subst k
    simp [outputTapes, counterTapes, Ne.symm different]
  · by_cases hc : k = counter
    · subst k
      simp [outputTapes, counterTapes, different]
    · simp [outputTapes, counterTapes, ho, hc, Ne.symm different]

theorem shape_after_counter {R : Type} (slot : (R ⊕ Fin 6) ↪ K)
    (counter : K) (outside : ∀ i, slot i ≠ counter) (base : K → List Bool)
    (values : R → Nat) (shape : registerTapes slot base values = base) (n : Nat) :
    registerTapes slot (counterTapes counter base n) values = counterTapes counter base n := by
  classical
  unfold counterTapes
  rw [RegisterFrameEmission.external_update slot base values counter outside, shape]

end BinPackingGap.PackingConstantPool

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobList
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPreparation

open GraphPackingRegisters PackingItemExpression

variable (fixed : InventoryData) (K : Nat)

def initialTapes (x : GraphReductionInput) : Tape fixed K → List Bool
  | .inr .input => graphBits x
  | _ => []

def baseTapes (x : GraphReductionInput) (reverseOutput : List Bool := []) :
    Tape fixed K → List Bool
  | .inr .input => graphBits x
  | .inr .endpoints => GraphFieldMachine.fieldBits .endpoints x
  | .inr .reverseOutput => reverseOutput
  | _ => []

def parsedOther (x : GraphReductionInput) : Other fixed K → Nat
  | .inl r => PackingSetupMachine.frame (parameters fixed K)
      (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k) (fun _ => 0) r
  | .inr _ => 0

def parsedTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingMachineLayout.tapes (Numerator fixed) denominator
    (baseTapes fixed K x) (fun _ => 0) (parsedOther fixed K x)

def setupOther (x : GraphReductionInput) (workValues : Work → Nat := fun _ => 0) :
    Other fixed K → Nat
  | .inl r => PackingSetupMachine.frame (parameters fixed K)
      (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k)
      (PackingSetupExpression.outputValues (parameters fixed K)
        x.graph.n x.graph.edges.length x.k) r
  | .inr r => workValues r

def repetitions (x : GraphReductionInput) : Nat :=
  100 * (fixed.P + x.graph.n * K + 1)

def geometryFactor : Nat :=
  160 * IntegerPackingArithmetic.widthRadix fixed.geometryBound ^ fixed.L

def preparedInputs (x : GraphReductionInput) : Variable → Nat
  | .vertexPower => 3 ^ x.graph.n
  | .totalPower => (repetitions fixed K x + 1) ^ x.graph.edges.length
  | .geometry => geometryFactor fixed *
      (repetitions fixed K x + 1) ^ x.graph.edges.length
  | _ => 0

def preparedWork : Work → Nat
  | .geometryFactor => geometryFactor fixed
  | _ => 0

def preparedOther (x : GraphReductionInput) : Other fixed K → Nat :=
  setupOther fixed K x (preparedWork fixed)

def binBound (x : GraphReductionInput) : Nat :=
  PackingSetupExpression.outputValues (parameters fixed K)
    x.graph.n x.graph.edges.length x.k .bins

def preparedTapes (x : GraphReductionInput) : Tape fixed K → List Bool :=
  PackingMachineLayout.tapes (Numerator fixed) denominator
    (baseTapes fixed K x (BinaryEncoding.natBits (binBound fixed K x)).reverse)
    (preparedInputs fixed K x) (preparedOther fixed K x)

end BinPackingGap.GraphPackingPreparation

namespace BinPackingGap.GraphPackingJobStream

open PackingDescriptorExpression PackingInventoryDescriptors

def endpointPower (D : InventoryData) (edge : D.Edge) (side : Fin 2) : Nat :=
  3 ^ ((D.graph.endpoint edge side).val + 1)

theorem values_update_label (D : InventoryData) (label : Option D.Vertex)
    (vertex : D.Vertex) (edge rep : Nat) :
    Function.update (values D label edge rep) .labelPower (3 ^ (vertex.val + 1)) =
      values D (some vertex) edge rep := by
  funext slot
  cases slot <;> simp [values, NaturalPackingNumerator.labelPower]

theorem nextInput_values (D : InventoryData) (label : Option D.Vertex)
    (edge : D.Edge) (rep : Nat) :
    PackingJobBody.nextInput (values D label edge.val rep) .labelPower .repetitionOne
        (endpointPower D edge 1) =
      values D (some (D.graph.endpoint edge 1)) edge.val (rep + 1) := by
  funext slot
  cases slot <;>
    simp [PackingJobBody.nextInput, values, endpointPower,
      NaturalPackingNumerator.labelPower]

end BinPackingGap.GraphPackingJobStream

namespace BinPackingGap.GraphPackingWidths

open GraphPackingRegisters GraphPackingPreparation
open BinaryRegisterProgram

variable (fixed : InventoryData) (K : Nat)

def treeScale : Nat := IntegerPackingArithmetic.widthRadix fixed.geometryBound ^ fixed.L

def geometryCoefficient : Nat :=
  GraphPackingBounds.repetitionCoefficient fixed.P K + 2 +
    Nat.size 160 + Nat.size (treeScale fixed)

end BinPackingGap.GraphPackingWidths

namespace BinPackingGap.GraphPackingJobs

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression

variable (fixed : InventoryData) (K : Nat)

def inventory (x : GraphReductionInput) : InventoryData :=
  PackingDescriptorExpression.instantiate fixed x.graph
    (GraphPackingPreparation.repetitions fixed K x) x.k

def inputs (x : GraphReductionInput) (edge : Nat) : Variable → Nat :=
  Function.update (preparedInputs fixed K x) .edgePower
    ((GraphPackingPreparation.repetitions fixed K x + 1) ^ edge)

@[simp] theorem inputs_label (x : GraphReductionInput) (edge : Nat) :
    inputs fixed K x edge .labelPower = 0 := rfl

@[simp] theorem inputs_repetition (x : GraphReductionInput) (edge : Nat) :
    inputs fixed K x edge .repetitionOne = 0 := rfl

@[simp] theorem inputs_edge (x : GraphReductionInput) (edge : Nat) :
    inputs fixed K x edge .edgePower =
      (GraphPackingPreparation.repetitions fixed K x + 1) ^ edge := by
  simp [inputs]

theorem inputs_eq_values (x : GraphReductionInput) (edge : Nat) :
    inputs fixed K x edge = PackingDescriptorExpression.values (inventory fixed K x) none edge 0 := by
  funext coordinate
  cases coordinate <;>
    simp [inputs, preparedInputs, PackingDescriptorExpression.values, inventory,
      PackingDescriptorExpression.instantiate, NaturalPackingNumerator.labelPower,
      InventoryData.coordinateDenominator, IntegerPackingArithmetic.geomDenominator,
      geometryFactor, InventoryData.geometryBound, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

def loadEndpoint (other : Other fixed K → Nat) (right : Bool) (v : Nat) : Other fixed K → Nat :=
  Function.update (Function.update other (.inr (endpointWork right)) v)
    (.inr (powerWork right)) (3 ^ (v + 1))

def loadedOther (x : GraphReductionInput) (left right : Nat) : Other fixed K → Nat :=
  loadEndpoint fixed K (loadEndpoint fixed K (preparedOther fixed K x) false left) true right

@[simp] theorem loaded_left (x : GraphReductionInput) (left right : Nat) :
    loadedOther fixed K x left right (.inr .leftPower) = 3 ^ (left + 1) := by
  simp [loadedOther, loadEndpoint, endpointWork, powerWork]

@[simp] theorem loaded_right (x : GraphReductionInput) (left right : Nat) :
    loadedOther fixed K x left right (.inr .rightPower) = 3 ^ (right + 1) := by
  simp [loadedOther, loadEndpoint, endpointWork, powerWork]

theorem loaded_setup (x : GraphReductionInput) (left right : Nat)
    (r : PackingSetupMachine.Reg (parameters fixed K)) :
    loadedOther fixed K x left right (.inl r) = preparedOther fixed K x (.inl r) := by
  simp [loadedOther, loadEndpoint]

theorem loaded_helper_zero (x : GraphReductionInput) (left right : Nat) (w : Work)
    (hw : w = .counter ∨ w = .one ∨ w = .temporary ∨ w = .reverse) :
    loadedOther fixed K x left right (.inr w) = 0 := by
  rcases hw with rfl | rfl | rfl | rfl <;>
    simp [loadedOther, loadEndpoint, endpointWork, powerWork, preparedOther,
      setupOther, preparedWork]

def completedInputs (x : GraphReductionInput) (edge right : Nat) : Variable → Nat :=
  Function.update (Function.update (inputs fixed K x edge) .labelPower (3 ^ (right + 1)))
    .repetitionOne (GraphPackingPreparation.repetitions fixed K x + 1)

def clearedOther (x : GraphReductionInput) (left right : Nat) : Other fixed K → Nat :=
  Function.update (Function.update (Function.update (Function.update
    (loadedOther fixed K x left right) (.inr .leftEndpoint) 0) (.inr .rightEndpoint) 0)
      (.inr .leftPower) 0) (.inr .rightPower) 0

theorem clearedOther_eq (x : GraphReductionInput) (left right : Nat) :
    clearedOther fixed K x left right = preparedOther fixed K x := by
  funext r
  cases r with
  | inl r => simp [clearedOther, loadedOther, loadEndpoint]
  | inr r =>
      cases r <;> simp [clearedOther, loadedOther, loadEndpoint, endpointWork, powerWork,
        preparedOther, setupOther, preparedWork]

theorem clearedInputs_eq (x : GraphReductionInput) (edge right : Nat) :
    Function.update (Function.update (Function.update (completedInputs fixed K x edge right)
      .edgePower ((GraphPackingPreparation.repetitions fixed K x + 1) ^ (edge + 1)))
      .labelPower 0) .repetitionOne 0 =
      inputs fixed K x (edge + 1) := by
  funext a
  cases a <;> simp [completedInputs, inputs, preparedInputs]

end BinPackingGap.GraphPackingJobs

namespace BinPackingGap.GraphPackingStockBounds

open scoped BigOperators

variable (fixed : InventoryData) (K : Nat)

def inventory (x : GraphReductionInput) : InventoryData :=
  PackingDescriptorExpression.instantiate fixed x.graph
    (GraphPackingPreparation.repetitions fixed K x) x.k

def stockCoefficient : Nat :=
  GraphPackingBounds.binCoefficient fixed.P K fixed.t fixed.d

def stockPolynomial : Polynomial Nat :=
  Polynomial.C (stockCoefficient fixed K) * (Polynomial.X + 1) ^ 2

@[simp] theorem stockPolynomial_eval (s : Nat) :
    (stockPolynomial fixed K).eval s = stockCoefficient fixed K * (s + 1) ^ 2 := by
  simp [stockPolynomial]

theorem binCount_le (x : GraphReductionInput) :
    (inventory fixed K x).B ≤ stockCoefficient fixed K * ((graphBits x).length + 1) ^ 2 := by
  rw [InventoryData.B_closed]
  exact GraphPackingBounds.bins_le_quadratic fixed.P K x.graph.n x.graph.edges.length
    fixed.t fixed.d (graphBits x).length
    (graph_vertexCount_le_bits x) (graph_edgeCount_le_bits x)

theorem globalStock_le (x : GraphReductionInput) (species : GlobalSpecies x.graph) :
    (inventory fixed K x).globalStock species ≤
      stockCoefficient fixed K * ((graphBits x).length + 1) ^ 2 := by
  let D := inventory fixed K x
  have hsum : (∑ s, D.globalStock s) = D.B := by
    simpa only [InventoryData.GlobalCopy, Fintype.card_sigma, Fintype.card_fin]
      using D.card_globalCopy x.k_le
  have hstock : D.globalStock species ≤ ∑ s, D.globalStock s :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ species)
  exact (hstock.trans_eq hsum).trans (binCount_le fixed K x)

theorem flagStock_le (x : GraphReductionInput) (species : FlagSpecies) :
    (inventory fixed K x).flagStock species ≤
      stockCoefficient fixed K * ((graphBits x).length + 1) ^ 2 := by
  let D := inventory fixed K x
  have hsum : (∑ s, D.flagStock s) = D.B := by
    simpa only [InventoryData.FlagCopy, Fintype.card_sigma, Fintype.card_fin]
      using D.card_flagCopy
  have hstock : D.flagStock species ≤ ∑ s, D.flagStock s :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ species)
  exact (hstock.trans_eq hsum).trans (binCount_le fixed K x)

theorem globalStock_le_polynomial (x : GraphReductionInput)
    (species : GlobalSpecies x.graph) :
    (inventory fixed K x).globalStock species ≤
      (stockPolynomial fixed K).eval (graphBits x).length := by
  rw [stockPolynomial_eval]
  exact globalStock_le fixed K x species

theorem flagStock_le_polynomial (x : GraphReductionInput) (species : FlagSpecies) :
    (inventory fixed K x).flagStock species ≤
      (stockPolynomial fixed K).eval (graphBits x).length := by
  rw [stockPolynomial_eval]
  exact flagStock_le fixed K x species

end BinPackingGap.GraphPackingStockBounds

namespace BinPackingGap.GraphPackingJobs

open BinaryEncoding PackingDescriptorExpression PackingInventoryDescriptors

theorem listBits_map {α β : Type} (encode : β → List Bool)
    (f : α → β) (xs : List α) :
    listBits encode (xs.map f) = listBits (fun a => encode (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, listBits, ih]

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparationFinish
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingEndpointPower

open BinPackingGames.Foundations.Complexity
open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks

variable {K : Type} [DecidableEq K]

theorem multiply_budget_le (v : Nat) :
    64 * ((3 : Nat).size + (3 ^ v).size + 1) ^ 2 ≤ 64 * (2 * v + 4) ^ 2 := by
  have hp := BinaryArithmetic.size_pow_le 3 v
  rw [size_three] at hp ⊢
  have hw : 2 + (3 ^ v).size + 1 ≤ 2 * v + 4 := by omega
  simpa only [pow_two] using Nat.mul_le_mul_left 64 (Nat.mul_le_mul hw hw)

omit [DecidableEq K] in
theorem register_frame_eq {Reg : Type} (slots : (Reg ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (vals : Reg → Nat)
    (registers : ∀ r, base (slots (.inl r)) = (vals r).bits)
    (scratch : ∀ j, base (slots (.inr j)) = []) : registerTapes slots base vals = base := by
  funext k
  by_cases hk : ∃ q, slots q = k
  · obtain ⟨q, rfl⟩ := hk
    cases q with
    | inl r => simpa only [registerTapes_reg] using (registers r).symm
    | inr j => simpa only [registerTapes_scratch] using (scratch j).symm
  · exact registerTapes_other slots base vals k hk

end BinPackingGap.PackingEndpointPower

namespace BinPackingGap.PackingVertexLoop

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

abbrev VertexTape (num : δ → Expr α) (den : Expr α) (Other Extra : Type) :=
  PackingMachineLayout.Tape num den Other Extra

theorem layout_external_update (num : δ → Expr α) (den : Expr α)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (external : Extra) (word : List Bool) :
    tapes num den (Function.update base (.inr external) word) input other =
      Function.update (tapes num den base input other) (.inr external) word := by
  apply RegisterFrameEmission.external_update
  intro i
  simp [registers]

theorem layout_output (num : δ → Expr α) (den : Expr α)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (output : Extra) (word : List Bool) :
    outputTapes (.inr output) (tapes num den base input other) word =
      tapes num den (outputTapes (.inr output) base word) input other := by
  unfold outputTapes
  rw [tapes_extra, layout_external_update]

theorem layout_counter (num : δ → Expr α) (den : Expr α)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (counter : Extra) (n : Nat) :
    tapes num den (counterTapes (.inr counter) base n) input other =
      counterTapes (.inr counter) (tapes num den base input other) n := by
  exact layout_external_update num den base input other counter (List.replicate n true)

theorem output_counter (num : δ → Expr α) (den : Expr α)
    (base : VertexTape num den Other Extra → List Bool) (output counter : Extra)
    (different : output ≠ counter) (word : List Bool) (n : Nat) :
    outputTapes (.inr output) (counterTapes (.inr counter) base n) word =
      counterTapes (.inr counter) (outputTapes (.inr output) base word) n := by
  funext k
  by_cases ho : k = .inr output
  · subst k
    simp [outputTapes, counterTapes, different]
  · by_cases hc : k = .inr counter
    · subst k
      simp [outputTapes, counterTapes, different, Ne.symm different]
    · simp [outputTapes, counterTapes, ho, hc]

end BinPackingGap.PackingVertexLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingStockStreams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingStockStreams

open PackingConstantPool PackingInventoryDescriptors PackingDescriptorExpression

theorem singleton_chunk_records (D : InventoryData) (label : Option D.Vertex)
    (edge rep : Nat) (descriptor : ItemDescriptor D) :
    PackingChunkMachine.records (numerator D) PackingItemExpression.denominator
      (fun _ => values D label edge rep) [descriptor] =
      rawRecord (rawOfDescriptor D label edge rep descriptor) := by
  simp only [PackingChunkMachine.records_cons, PackingChunkMachine.records_nil,
    List.append_nil, record_eq]

end BinPackingGap.GraphPackingStockStreams

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_LocalTemplateBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

def localTemplateItems {v : D.Vertex} (row : D.RowAt v) (anchor : D.AnchorAt v)
    (u : D.GlobalCopy) (l : D.LocalAt v) (flag : D.FlagCopy) : Role → D.Item
  | .x => ⟨.x, ⟨v, row⟩⟩
  | .anchor => ⟨.anchor, ⟨v, anchor⟩⟩
  | .«global» => ⟨.«global», u⟩
  | .«local» => ⟨.«local», ⟨v, l⟩⟩
  | .flag => ⟨.flag, flag⟩

@[simp] theorem localTemplateItems_role {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (r : Role) :
    D.itemRole (D.localTemplateItems row anchor u l flag r) = r := by
  cases r <;> rfl

@[simp] theorem localTemplateItems_label {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (r : Role) :
    D.itemLabel (D.localTemplateItems row anchor u l flag r) =
      tableRoleLabel v v v r := by
  cases r <;> rfl

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

abbrev Template := Σ v : D.Vertex, Bool × D.LocalBin v

end BinPackingGap.InventoryData

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionValidationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionValidationMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition

theorem fractionExit (a d : Nat) :
    orderExit .fraction (BinaryOrderMachine.orderNat a d .eq) =
      some (if a ≤ d then .number .assigned .scan else .control .reject) := by
  unfold BinaryOrderMachine.orderNat
  split_ifs <;> simp_all [orderExit] <;> omega

theorem boundExit (j bins : Nat) :
    orderExit .bound (BinaryOrderMachine.orderNat j bins .eq) =
      some (if j < bins then .control .clearNumerator else .control .reject) := by
  unfold BinaryOrderMachine.orderNat
  split_ifs <;> simp_all [orderExit]

end BinPackingGap.ExtensionValidationMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_ExtensionVerifierMachine
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.ExtensionVerifierMachine.Fields

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer

theorem run_nat (field : Field) (n : Nat) (suffix : List Bool) (words : Words) :
    run (.flag field) words (BinaryEncoding.natBits n ++ suffix) =
      run (afterField field)
        (prepend words field.block (BinaryEncoding.natBits n).reverse) suffix :=
  run_frame field n.bits suffix words

theorem run_items (items : RawInstance) (suffix : List Bool) (words : Words) :
    run .items words (BinaryEncoding.rawInstanceBits items ++ suffix) =
      run .fixed
        (prepend words .items (BinaryEncoding.rawInstanceBits items).reverse) suffix := by
  induction items generalizing words with
  | nil => simp [BinaryEncoding.rawInstanceBits, BinaryEncoding.listBits, run,
      nextMode, Mode.block]
  | cons item items ih =>
      change run (.flag .numerator) (prepend words .items [true])
        (BinaryEncoding.natBits item.1 ++ BinaryEncoding.natBits item.2 ++
          BinaryEncoding.rawInstanceBits items ++ suffix) = _
      simp only [List.append_assoc]
      rw [run_nat]
      change run (.flag .denominator)
        (prepend (prepend words .items [true]) .items
          (BinaryEncoding.natBits item.1).reverse)
        (BinaryEncoding.natBits item.2 ++
          (BinaryEncoding.rawInstanceBits items ++ suffix)) = _
      rw [run_nat]
      change run .items _ (BinaryEncoding.rawInstanceBits items ++ suffix) = _
      rw [ih]
      simp only [Field.block, prepend_prepend, BinaryEncoding.rawInstanceBits,
        BinaryEncoding.listBits, BinaryEncoding.pairBits, List.reverse_cons,
        List.reverse_append, List.append_assoc]

def encodedWords (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) : Words
  | .bins => BinaryEncoding.natBits bins
  | .items => BinaryEncoding.rawInstanceBits items
  | .fixed => BinaryEncoding.listBits (BinaryEncoding.optionBits BinaryEncoding.natBits) fixed

theorem run_extension (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) :
    run (.flag .bins) empty (BinaryEncoding.extensionBits bins items fixed) =
      (.fixed, reversed (encodedWords bins items fixed)) := by
  unfold BinaryEncoding.extensionBits
  rw [List.append_assoc, run_nat]
  change run .items _ (_ ++ _) = _
  rw [run_items, run_fixed]
  congr 1
  funext block
  cases block <;> simp [prepend, empty, reversed, encodedWords, Field.block]

def savedTape : Block → Fin 7
  | .bins => 1
  | .items => 2
  | .fixed => 3

def outputTape : Block → Fin 7
  | .bins => 4
  | .items => 5
  | .fixed => 6

theorem update_saved (input : List Bool) (saved output : Words)
    (block : Block) (replacement : List Bool) :
    Function.update (tapes input saved output) (savedTape block) replacement =
      tapes input (Function.update saved block replacement) output := by
  funext k; cases block <;> fin_cases k <;> rfl

theorem update_output (input : List Bool) (saved output : Words)
    (block : Block) (replacement : List Bool) :
    Function.update (tapes input saved output) (outputTape block) replacement =
      tapes input saved (Function.update output block replacement) := by
  funext k; cases block <;> fin_cases k <;> rfl

theorem step_scan_cons (bit : Bool) (input : List Bool) (saved output : Words)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) (bit :: input) saved output mode register) =
      some (cfg (some .scan) input (prepend saved mode.block [bit]) output
        (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  cases mode with
  | flag field =>
      cases field <;>
        simp [instruction, scanFinish, cfg, TM2.stepAux, Mode.block, Field.block,
          update_input, ← update_saved, savedTape, prepend, tapes] <;> rfl
  | digit field =>
      cases field <;>
        simp [instruction, scanFinish, cfg, TM2.stepAux, Mode.block, Field.block,
          update_input, ← update_saved, savedTape, prepend, tapes] <;> rfl
  | items =>
      simp [instruction, scanFinish, cfg, TM2.stepAux, Mode.block,
        update_input, ← update_saved, savedTape, prepend, tapes]; rfl
  | fixed =>
      simp [instruction, scanFinish, cfg, TM2.stepAux, Mode.block,
        update_input, ← update_saved, savedTape, prepend, tapes]; rfl

theorem scanTrace (input : List Bool) (saved output : Words) (mode : Mode)
    (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .scan) input saved output mode register)) =
      some (cfg (some .restoreBins) [] (run mode saved input).2 output) := by
  induction input generalizing mode saved register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run] using step_scan_empty saved output mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run] using ih (saved := prepend saved mode.block [bit])
        (mode := nextMode mode bit) (register := none)

theorem scan_extension (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) :
    (advance machine.step)^[(BinaryEncoding.extensionBits bins items fixed).length + 1]
      (some (initList machine (BinaryEncoding.extensionBits bins items fixed))) =
      some (cfg (some .restoreBins) [] (reversed (encodedWords bins items fixed)) empty) := by
  rw [initList_eq]
  simpa only [run_extension] using
    scanTrace (BinaryEncoding.extensionBits bins items fixed) empty empty (.flag .bins) none

def restoreLabel : Block → Label
  | .bins => .restoreBins
  | .items => .restoreItems
  | .fixed => .restoreFixed

def nextRestore : Block → Option Label
  | .bins => some .restoreItems
  | .items => some .restoreFixed
  | .fixed => none

theorem restoreTrace (block : Block) (saved output : Words) :
    (advance machine.step)^[(saved block).length + 1]
      (some (cfg (some (restoreLabel block)) [] saved output)) =
      some (cfg (nextRestore block) [] (Function.update saved block [])
        (prepend output block (saved block).reverse)) := by
  change (nextAt (outputTape block) instruction)^[(saved block).length + 1]
    (some (cfg (some (restoreLabel block)) [] saved output)) =
    some (cfg (nextRestore block) [] (Function.update saved block [])
      (prepend output block (saved block).reverse))
  have distinct : savedTape block ≠ outputTape block := by cases block <;> decide
  have atLoop : instruction (restoreLabel block) =
      loopAt (savedTape block) (outputTape block) id false
        (restoreLabel block) (nextRestore block) := by cases block <;> rfl
  have trace := transferAt_fromTapes (savedTape block) (outputTape block) distinct
    id false (restoreLabel block) (nextRestore block) instruction atLoop
    (tapes [] saved output) (Mode.flag .bins) none
  have source : tapes [] saved output (savedTape block) = saved block := by
    cases block <;> rfl
  have destination : tapes [] saved output (outputTape block) = output block := by
    cases block <;> rfl
  rw [source, destination] at trace
  simpa only [cfg, tapesAt, update_saved, update_output,
    List.map_id_fun, id_eq, prepend] using! trace

theorem restoreAllTrace (words : Words) :
    (advance machine.step)^[(words .bins).length + (words .items).length +
        (words .fixed).length + 3]
      (some (cfg (some .restoreBins) [] (reversed words) empty)) =
      some (cfg none [] empty words) := by
  let saved₁ := Function.update (reversed words) .bins []
  let output₁ := prepend empty .bins (words .bins)
  let saved₂ := Function.update saved₁ .items []
  let output₂ := prepend output₁ .items (words .items)
  have first := restoreTrace .bins (reversed words) empty
  have second := restoreTrace .items saved₁ output₁
  have third := restoreTrace .fixed saved₂ output₂
  simp only [reversed, List.length_reverse, List.reverse_reverse,
    restoreLabel, nextRestore] at first
  change (advance machine.step)^[(words .bins).length + 1]
    (some (cfg (some .restoreBins) [] (reversed words) empty)) =
    some (cfg (some .restoreItems) [] saved₁ output₁) at first
  have saved₁_items : saved₁ .items = (words .items).reverse := by
    simp [saved₁, reversed]
  have saved₂_fixed : saved₂ .fixed = (words .fixed).reverse := by
    simp [saved₂, saved₁, reversed]
  rw [saved₁_items] at second
  simp only [List.length_reverse, List.reverse_reverse, restoreLabel, nextRestore] at second
  change (advance machine.step)^[(words .items).length + 1]
    (some (cfg (some .restoreItems) [] saved₁ output₁)) =
    some (cfg (some .restoreFixed) [] saved₂ output₂) at second
  rw [saved₂_fixed] at third
  simp only [List.length_reverse, List.reverse_reverse, restoreLabel, nextRestore] at third
  have cleared : Function.update saved₂ .fixed [] = empty := by
    funext block; cases block <;> simp [saved₂, saved₁, empty]
  have restored : prepend output₂ .fixed (words .fixed) = words := by
    funext block; cases block <;> simp [output₂, output₁, prepend, empty]
  rw [cleared, restored] at third
  have total := appendTrace (advance machine.step)
    (appendTrace (advance machine.step) first second) third
  have clock : (words .bins).length + (words .items).length +
      (words .fixed).length + 3 =
      ((words .bins).length + 1 + ((words .items).length + 1)) +
        ((words .fixed).length + 1) := by omega
  rw [clock]
  exact total

theorem extensionTrace (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) :
    (advance machine.step)^[2 * (BinaryEncoding.extensionBits bins items fixed).length + 4]
      (some (initList machine (BinaryEncoding.extensionBits bins items fixed))) =
      some (cfg none [] empty (encodedWords bins items fixed)) := by
  have first := scan_extension bins items fixed
  have second := restoreAllTrace (encodedWords bins items fixed)
  have joined := appendTrace (advance machine.step) first second
  have length : (BinaryEncoding.extensionBits bins items fixed).length =
      (encodedWords bins items fixed .bins).length +
      (encodedWords bins items fixed .items).length +
      (encodedWords bins items fixed .fixed).length := by
    simp [BinaryEncoding.extensionBits, encodedWords, Nat.add_assoc]
  have clock : 2 * (BinaryEncoding.extensionBits bins items fixed).length + 4 =
      (BinaryEncoding.extensionBits bins items fixed).length + 1 +
        ((encodedWords bins items fixed .bins).length +
          (encodedWords bins items fixed .items).length +
          (encodedWords bins items fixed .fixed).length + 3) := by omega
  rw [clock]
  exact joined

def extensionInTime (bins : Nat) (items : RawInstance) (fixed : List (Option Nat)) :
    StateTransition.EvalsToInTime machine.step
      (initList machine (BinaryEncoding.extensionBits bins items fixed))
      (some (cfg none [] empty (encodedWords bins items fixed)))
      (2 * (BinaryEncoding.extensionBits bins items fixed).length + 4) where
  steps := 2 * (BinaryEncoding.extensionBits bins items fixed).length + 4
  evals_in_steps := extensionTrace bins items fixed
  steps_le_m := Nat.le_refl _

end BinPackingGap.ExtensionVerifierMachine.Fields

end OAI
end


