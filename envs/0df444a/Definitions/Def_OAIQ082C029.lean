-- Prove2me | Definitions.Def_OAIQ082C029
-- name    : OAIQ082C029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:22:45.611219+00:00
-- url     : https://prove2.me/theorems/33aa7d6f-85d2-4eb1-b779-64f1b46a8372
-- title:
--   Definitions bundle OAIQ082C029 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 84 declarations of OpenAI's Lean: 24 definitions and 60 theorems. The definitions and types are `OAI.BinPackingGap.GraphPackingJobs.cleanupTimePolynomial`, `OAI.BinPackingGap.GraphPackingJobs.edgeTimePolynomial`, `OAI.BinPackingGap.GraphPackingJobs.loopTimePolynomial`, `OAI.BinPackingGap.GraphPackingJobs.repeatTimePolynomial`, `OAI.BinPackingGap.GraphPackingJobs.setupBound`, `OAI.BinPackingGap.GraphPackingJobs.setupTimePolynomial`, `OAI.BinPackingGap.GraphPackingJobs.timePolynomial`, `OAI.BinPackingGap.GraphPackingPreparation.arithmeticPolynomial`, `OAI.BinPackingGap.GraphPackingPreparation.finishPolynomial`, `OAI.BinPackingGap.GraphPackingPreparation.geometryPolynomial`, `OAI.BinPackingGap.GraphPackingPreparation.headerPolynomial`, `OAI.BinPackingGap.GraphPackingPreparation.powerPolynomial`, `OAI.BinPackingGap.GraphPackingPreparation.timePolynomial`, `OAI.BinPackingGap.GraphPackingRun.prefixTimePolynomial`, `OAI.BinPackingGap.GraphPackingRun.terminalRun`, `OAI.BinPackingGap.GraphPackingRun.timePolynomial`, `OAI.BinPackingGap.GraphPackingRun.wordTimePolynomial`, `OAI.BinPackingGap.GraphPackingVerticesBound.polynomial`, `OAI.BinPackingGap.SearchStageMachines.stages`, `OAI.BinPackingGap.SearchUpdateMachine.computation`, `OAI.BinPackingGap.SearchUpdateMachine.fillSteps`, `OAI.BinPackingGap.SearchUpdateMachine.rawRun`, `OAI.BinPackingGap.absoluteAdditiveAlgorithm_of_pEqualsNP`, `OAI.BinPackingGap.graphPackingComputation`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`BinPacking_Machines_GraphPackingGlobalExecution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingGlobalExecution.lean), [`BinPacking_Machines_GraphPackingJobCleanup`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingJobCleanup.lean), [`BinPacking_Machines_GraphPackingJobEdge`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingJobEdge.lean), [`BinPacking_Machines_GraphPackingJobList`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingJobList.lean), [`BinPacking_Machines_GraphPackingMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingMachine.lean), [`BinPacking_Machines_GraphPackingPreparation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingPreparation.lean), [`BinPacking_Machines_GraphPackingPreparationFinish`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingPreparationFinish.lean), [`BinPacking_Machines_GraphPackingVerticesBound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingVerticesBound.lean), [`BinPacking_Machines_PackingVertexUpdate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/PackingVertexUpdate.lean), [`BinPacking_Results_OptimalSearch`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Results/OptimalSearch.lean), [`BinPacking_Search_SearchStageMachines`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchStageMachines.lean), [`BinPacking_Search_SearchUpdateMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchUpdateMachine.lean).
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C027` and `OAIQ082C028` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.BinPackingGap.main_results`, `OAI_BinPackingGap_packingGapNPHard` and `OAI.BinPackingGap.packingGapNPHard_oaiq082`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C027
import Definitions.Def_OAIQ082C028

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingVertexUpdate
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingLayoutCommands

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open PackingMachineLayout

variable {Descriptor Input Other Extra : Type}
variable [DecidableEq Descriptor] [DecidableEq Input] [DecidableEq Other] [DecidableEq Extra]

theorem setOther_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Other) (constant : Nat) (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (state : State) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ (setOtherTime num den destination constant).eval width,
      Exec (setOther num den destination constant)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den base input (Function.update other destination constant)⟩ := by
  have run := PackingAssignments.constant_exec (registers (Extra := Extra) num den)
    (others num den destination) constant base (values num den input other) state width
    (values_width num den input other width hi ho)
  rw [← values_update_other] at run
  simpa only [setOther, setOtherTime, Polynomial.eval_add, Polynomial.eval_ofNat, tapes] using run

end BinPackingGap.PackingLayoutCommands

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobList
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingWidths

open GraphPackingRegisters GraphPackingPreparation
open BinaryRegisterProgram

variable (fixed : InventoryData) (K : Nat)

theorem setup_width (x : GraphReductionInput) :
    ∀ r, (PackingSetupMachine.frame (parameters fixed K)
      (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k)
      (PackingSetupExpression.outputValues (parameters fixed K)
        x.graph.n x.graph.edges.length x.k) r).size ≤ width fixed K x := by
  let p := parameters fixed K
  let initial := PackingSetupMachine.frame p
    (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k) (fun _ => 0)
  have hi : ∀ r, (initial r).size ≤ (graphBits x).length := by
    intro r
    rcases r with a | (o | temp)
    · cases a with
      | n => exact (nat_size_le_self _).trans (graph_vertexCount_le_bits x)
      | m => exact (nat_size_le_self _).trans (graph_edgeCount_le_bits x)
      | k =>
          exact (nat_size_le_self _).trans
            (x.k_le.trans (graph_vertexCount_le_bits x))
    · simp [initial, PackingSetupMachine.frame]
    · simp [initial, PackingSetupMachine.frame]
  have h := BinaryRegisterStructured.final_width (PackingSetupMachine.commands p) initial
    (graphBits x).length hi
  rw [(PackingSetupMachine.commands_correct p x.graph.n x.graph.edges.length x.k).2] at h
  intro r
  have hr := h r
  rw [← setupPolynomial_eval fixed K] at hr
  unfold width
  rw [polynomial_eval]
  exact hr.trans (by omega)

theorem preparedInputs_width (x : GraphReductionInput) :
    ∀ a, (preparedInputs fixed K x a).size ≤ width fixed K x := by
  intro a
  cases a with
  | vertexPower => exact vertex_power_width fixed K x x.graph.n (by omega)
  | geometry => exact geometry_width fixed K x
  | totalPower => exact edge_power_width fixed K x x.graph.edges.length le_rfl
  | labelPower => simp [preparedInputs]
  | edgePower => simp [preparedInputs]
  | repetitionOne => simp [preparedInputs]

theorem preparedOther_width (x : GraphReductionInput) :
    ∀ r, (preparedOther fixed K x r).size ≤ width fixed K x := by
  intro r
  cases r with
  | inl r => exact setup_width fixed K x r
  | inr r => exact preparedWork_width fixed K x r

theorem repetitions_width (x : GraphReductionInput) :
    GraphPackingPreparation.repetitions fixed K x + 1 ≤ width fixed K x := by
  have h := GraphPackingBounds.repetitions_le_linear fixed.P K x.graph.n (graphBits x).length
    (graph_vertexCount_le_bits x)
  change GraphPackingPreparation.repetitions fixed K x ≤ _ at h
  unfold width
  rw [polynomial_eval]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at h ⊢
  omega

theorem small_constant_width (x : GraphReductionInput) : 3 ≤ width fixed K x := by
  unfold width
  rw [polynomial_eval]
  omega

theorem input_length_le_width (x : GraphReductionInput) :
    (graphBits x).length + 1 ≤ width fixed K x := by
  unfold width
  rw [polynomial_eval]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem update_width {α : Type} [DecidableEq α] (x : GraphReductionInput)
    (values : α → Nat) (h : ∀ a, (values a).size ≤ width fixed K x)
    (a : α) (v : Nat) (hv : v.size ≤ width fixed K x) :
    ∀ b, (Function.update values a v b).size ≤ width fixed K x := by
  intro b
  by_cases hb : b = a
  · subst b; simpa only [Function.update_self] using hv
  · simpa only [Function.update_of_ne hb] using h b

end BinPackingGap.GraphPackingWidths

namespace BinPackingGap.GraphPackingJobs

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression

variable (fixed : InventoryData) (K : Nat)

theorem inputs_width (x : GraphReductionInput) (edge : Nat) (he : edge ≤ x.graph.edges.length) :
    ∀ a, (inputs fixed K x edge a).size ≤ GraphPackingWidths.width fixed K x :=
  GraphPackingWidths.update_width fixed K x _
    (GraphPackingWidths.preparedInputs_width fixed K x) .edgePower _
    (GraphPackingWidths.edge_power_width fixed K x edge he)

theorem loadEndpoint_width (x : GraphReductionInput) (other : Other fixed K → Nat)
    (hother : ∀ r, (other r).size ≤ GraphPackingWidths.width fixed K x)
    (right : Bool) (v : Nat) (hv : v < x.graph.n) :
    ∀ r, (loadEndpoint fixed K other right v r).size ≤ GraphPackingWidths.width fixed K x := by
  have hvsize : v.size ≤ GraphPackingWidths.width fixed K x :=
    (nat_size_le_self v).trans
      ((Nat.le_of_lt hv).trans ((graph_vertexCount_le_bits x).trans
        ((Nat.le_succ _).trans (GraphPackingWidths.input_length_le_width fixed K x))))
  apply GraphPackingWidths.update_width fixed K x
  · exact GraphPackingWidths.update_width fixed K x other hother _ v hvsize
  · exact GraphPackingWidths.vertex_power_width fixed K x (v + 1) (by omega)

theorem loadedOther_width (x : GraphReductionInput) (left right : Nat)
    (hl : left < x.graph.n) (hr : right < x.graph.n) :
    ∀ r, (loadedOther fixed K x left right r).size ≤ GraphPackingWidths.width fixed K x := by
  exact loadEndpoint_width fixed K x _
    (loadEndpoint_width fixed K x _ (GraphPackingWidths.preparedOther_width fixed K x)
      false left hl) true right hr

theorem completedInputs_width (x : GraphReductionInput) (edge right : Nat)
    (he : edge ≤ x.graph.edges.length) (hr : right < x.graph.n) :
    ∀ a, (completedInputs fixed K x edge right a).size ≤ GraphPackingWidths.width fixed K x := by
  apply GraphPackingWidths.update_width fixed K x
  · exact GraphPackingWidths.update_width fixed K x _ (inputs_width fixed K x edge he)
      .labelPower _ (GraphPackingWidths.vertex_power_width fixed K x (right + 1) (by omega))
  · exact (nat_size_le_self _).trans (GraphPackingWidths.repetitions_width fixed K x)

end BinPackingGap.GraphPackingJobs

namespace BinPackingGap.GraphPackingStockBounds

open scoped BigOperators

variable (fixed : InventoryData) (K : Nat)

theorem preparedOther_size_le (x : GraphReductionInput)
    (register : GraphPackingRegisters.Other fixed K) :
    (GraphPackingPreparation.preparedOther fixed K x register).size ≤
      widthCoefficient fixed K * ((graphBits x).length + 1) ^ 2 :=
  (GraphPackingWidths.preparedOther_width fixed K x register).trans
    (preparationWidth_le fixed K x)

theorem preparedOther_size_le_polynomial (x : GraphReductionInput)
    (register : GraphPackingRegisters.Other fixed K) :
    (GraphPackingPreparation.preparedOther fixed K x register).size ≤
      (widthPolynomial fixed K).eval (graphBits x).length := by
  rw [widthPolynomial_eval]
  exact preparedOther_size_le fixed K x register

end BinPackingGap.GraphPackingStockBounds

namespace BinPackingGap.GraphPackingJobs

section

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open PackingDescriptorExpression PackingInventoryDescriptors

variable (fixed : InventoryData) (K : Nat)

theorem repeatInputs_width (x : GraphReductionInput) (edge : Nat)
    (he : edge ≤ x.graph.edges.length) :
    ∀ a, (repeatInputs fixed K x edge a).size ≤ GraphPackingWidths.width fixed K x := by
  apply GraphPackingWidths.update_width fixed K x _ (inputs_width fixed K x edge he)
    .repetitionOne 1
  simp only [Nat.size_one]
  have h := GraphPackingWidths.small_constant_width fixed K x
  omega

end

open BinaryEncoding PackingDescriptorExpression PackingInventoryDescriptors

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparationFinish
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPreparation

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

variable (fixed : InventoryData) (K : Nat)

theorem setupValues_width (x : GraphReductionInput) :
    ∀ r, (setupValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x := by
  apply PackingLayoutCommands.values_width
  · intro a; simp
  · intro a
    cases a with
    | inl r => exact GraphPackingWidths.setup_width fixed K x r
    | inr r => simp [setupOther]

theorem firstPowerValues_width (x : GraphReductionInput) :
    ∀ r, (firstPowerValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x :=
  GraphPackingWidths.update_width fixed K x _ (setupValues_width fixed K x) _ _
    (GraphPackingWidths.vertex_power_width fixed K x x.graph.n (by omega))

theorem secondPowerValues_width (x : GraphReductionInput) :
    ∀ r, (secondPowerValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x :=
  GraphPackingWidths.update_width fixed K x _ (firstPowerValues_width fixed K x) _ _
    (GraphPackingWidths.edge_power_width fixed K x x.graph.edges.length le_rfl)

theorem factorValues_width (x : GraphReductionInput) :
    ∀ r, (factorValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x :=
  GraphPackingWidths.update_width fixed K x _ (secondPowerValues_width fixed K x) _ _
    (GraphPackingWidths.preparedWork_width fixed K x .geometryFactor)

theorem finalValues_width (x : GraphReductionInput) :
    ∀ r, (finalValues fixed K x r).size ≤ GraphPackingWidths.width fixed K x := by
  rw [finalValues_eq]
  exact PackingLayoutCommands.values_width _ _ _ _ _
    (GraphPackingWidths.preparedInputs_width fixed K x)
    (GraphPackingWidths.preparedOther_width fixed K x)

def geometryPolynomial : Polynomial Nat :=
  (runtimePolynomial (PackingAssignments.constantCommands (work fixed K .geometryFactor)
      (geometryFactor fixed)) +
    runtimePolynomial [.mul (geometryOperands fixed K)] + 5).comp
      (GraphPackingWidths.polynomial fixed K)

theorem geometry_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (geometryPolynomial fixed K).eval (graphBits x).length,
      Exec (geometry fixed K)
        ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (secondPowerValues fixed K x)⟩
        steps ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K) (baseTapes fixed K x) (finalValues fixed K x)⟩ := by
  obtain ⟨a, ha, arun⟩ := PackingAssignments.constant_exec (slots fixed K)
    (work fixed K .geometryFactor) (geometryFactor fixed) (baseTapes fixed K x)
    (secondPowerValues fixed K x) state (GraphPackingWidths.width fixed K x)
    (secondPowerValues_width fixed K x)
  have ready : Ready [.mul (geometryOperands fixed K)] (factorValues fixed K x) := by
    simp [Ready, commandReady, destination, geometryOperands, factorValues, secondPowerValues,
      firstPowerValues, setupValues, work_register, item_register, PackingMachineLayout.values]
  have mulResult : resultOf [.mul (geometryOperands fixed K)] (factorValues fixed K x) =
      finalValues fixed K x := by
    rw [resultOf_cons, resultOf_nil]
    simp [result, destination, value, geometryOperands,
      finalValues, factorValues, secondPowerValues, firstPowerValues,
      work_register, item_register]
  obtain ⟨b, hb, brun⟩ := PackingAssignments.exec (slots fixed K)
    [.mul (geometryOperands fixed K)] (baseTapes fixed K x) (factorValues fixed K x)
    ready (.arithmetic (BinaryAddMachine.clean ())) (GraphPackingWidths.width fixed K x)
    (factorValues_width fixed K x)
  rw [mulResult] at brun
  have first : Exec (setWork fixed K .geometryFactor (geometryFactor fixed))
      ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (secondPowerValues fixed K x)⟩ a
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        registerTapes (slots fixed K) (baseTapes fixed K x) (factorValues fixed K x)⟩ := arun
  refine ⟨a + b + 1, ?_, ?_⟩
  · simp only [geometryPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_ofNat]
    dsimp only [GraphPackingWidths.width] at ha hb
    omega
  · exact (PhaseRuns.cons first (PhaseRuns.single brun)).toExec

def headerPolynomial : Polynomial Nat :=
  (runtimePolynomial (PackingAssignments.copyCommands (work fixed K .header)
    (output fixed K .bins) (headerDifferent fixed K)) + Polynomial.X + 5).comp
      (GraphPackingWidths.polynomial fixed K)

theorem header_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (headerPolynomial fixed K).eval (graphBits x).length,
      Exec (header fixed K)
        ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (finalValues fixed K x)⟩
        steps ⟨.arithmetic (BinaryAddMachine.clean ()), preparedTapes fixed K x⟩ := by
  let vals := finalValues fixed K x
  let filled := Function.update vals (work fixed K .header) (binBound fixed K x)
  have bins : vals (output fixed K .bins) = binBound fixed K x := by
    rw [show vals = finalValues fixed K x from rfl, finalValues_eq]
    rfl
  have empty : vals (work fixed K .header) = 0 := by
    rw [show vals = finalValues fixed K x from rfl, finalValues_eq]
    rfl
  obtain ⟨a, ha, arun⟩ := PackingAssignments.copy_exec (slots fixed K)
    (work fixed K .header) (output fixed K .bins) (headerDifferent fixed K)
    (baseTapes fixed K x) vals state (GraphPackingWidths.width fixed K x)
    (finalValues_width fixed K x)
  rw [bins] at arun
  have cleared : Function.update filled (work fixed K .header) 0 = vals := by
    change Function.update
      (Function.update vals (work fixed K .header) (binBound fixed K x))
      (work fixed K .header) 0 = vals
    rw [Function.update_idem]
    exact Function.update_eq_self_iff.mpr empty.symm
  have baseUpdate : Function.update (baseTapes fixed K x) (.inr .reverseOutput)
      ((BinaryEncoding.natBits (binBound fixed K x)).reverse ++
        baseTapes fixed K x [] (.inr .reverseOutput)) =
      baseTapes fixed K x (BinaryEncoding.natBits (binBound fixed K x)).reverse := by
    funext t
    rcases t with r | e
    · simp [baseTapes]
    · cases e <;> simp [baseTapes]
  have native := RegisterFrameEmission.exec (slots fixed K) (baseTapes fixed K x)
    filled (work fixed K .header) (.inr .reverseOutput) (by intro i; simp [slots, PackingMachineLayout.registers]) ()
  have filledHeader : filled (work fixed K .header) = binBound fixed K x := by simp [filled]
  rw [filledHeader, cleared, baseUpdate] at native
  have emitted := PackingArithmeticProgram.exec _ _ _ _
    (.arithmetic (BinaryAddMachine.clean ())) native
  have finalFrame : registerTapes (slots fixed K)
      (baseTapes fixed K x (BinaryEncoding.natBits (binBound fixed K x)).reverse) vals =
      preparedTapes fixed K x := by
    rw [show vals = finalValues fixed K x from rfl, finalValues_eq]
    rfl
  rw [finalFrame] at emitted
  have binWidth : (binBound fixed K x).size ≤ GraphPackingWidths.width fixed K x :=
    GraphPackingWidths.setup_width fixed K x (PackingSetupMachine.output (parameters fixed K) .bins)
  refine ⟨a + (1 + ((binBound fixed K x).size + 1)) + 1, ?_, ?_⟩
  · simp only [headerPolynomial, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    dsimp only [GraphPackingWidths.width] at ha binWidth
    omega
  · exact (PhaseRuns.cons arun (PhaseRuns.single emitted)).toExec

def finishPolynomial : Polynomial Nat := geometryPolynomial fixed K + headerPolynomial fixed K

theorem finish_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (finishPolynomial fixed K).eval (graphBits x).length,
      PhaseRuns [geometry fixed K, header fixed K]
        ⟨state, registerTapes (slots fixed K) (baseTapes fixed K x) (secondPowerValues fixed K x)⟩
        steps ⟨.arithmetic (BinaryAddMachine.clean ()), preparedTapes fixed K x⟩ := by
  obtain ⟨a, ha, arun⟩ := geometry_exec fixed K x state
  obtain ⟨b, hb, brun⟩ := header_exec fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  exact ⟨a + b, by simpa only [finishPolynomial, Polynomial.eval_add] using Nat.add_le_add ha hb,
    PhaseRuns.cons arun (PhaseRuns.single brun)⟩

end BinPackingGap.GraphPackingPreparation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobCleanup
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)

variable (fixed : InventoryData) (K : Nat)

def cleanupTimePolynomial : Polynomial Nat :=
  (cleanupWidthTimePolynomial fixed K).comp (GraphPackingWidths.polynomial fixed K)

theorem cleanup_exec (x : GraphReductionInput) (e : x.graph.Edge)
    (base : Tape fixed K → List Bool) (state : State) :
    ∃ steps ≤ (cleanupTimePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (cleanupPhases fixed K)
        ⟨state, tapes (Numerator fixed) denominator base
          (completedInputs fixed K x e.val (x.graph.right e).val)
          (loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator base (inputs fixed K x (e.val + 1))
            (preparedOther fixed K x)⟩ := by
  let width := GraphPackingWidths.width fixed K x
  let initialInput := completedInputs fixed K x e.val (x.graph.right e).val
  let initialOther := loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val
  let nextPower := (GraphPackingPreparation.repetitions fixed K x + 1) ^ (e.val + 1)
  let advancedInput := Function.update initialInput .edgePower nextPower
  let other₁ := Function.update initialOther (.inr Work.leftEndpoint) 0
  let other₂ := Function.update other₁ (.inr Work.rightEndpoint) 0
  let other₃ := Function.update other₂ (.inr Work.leftPower) 0
  let other₄ := Function.update other₃ (.inr Work.rightPower) 0
  let input₁ := Function.update advancedInput .labelPower 0
  let input₂ := Function.update input₁ .repetitionOne 0
  let clean : State := .arithmetic (BinaryAddMachine.clean ())
  have initialInputWidth : ∀ a, (initialInput a).size ≤ width :=
    completedInputs_width fixed K x e.val (x.graph.right e).val
      (Nat.le_of_lt e.isLt) (x.graph.right e).isLt
  have initialOtherWidth : ∀ r, (initialOther r).size ≤ width :=
    loadedOther_width fixed K x (x.graph.left e).val (x.graph.right e).val
      (x.graph.left e).isLt (x.graph.right e).isLt
  have zeroWidth : (0 : Nat).size ≤ width := by simp
  have advancedInputWidth : ∀ a, (advancedInput a).size ≤ width :=
    GraphPackingWidths.update_width fixed K x initialInput initialInputWidth .edgePower
      nextPower (GraphPackingWidths.edge_power_width fixed K x (e.val + 1)
        (Nat.succ_le_of_lt e.isLt))
  have other₁Width : ∀ r, (other₁ r).size ≤ width :=
    GraphPackingWidths.update_width fixed K x initialOther initialOtherWidth _ 0 zeroWidth
  have other₂Width : ∀ r, (other₂ r).size ≤ width :=
    GraphPackingWidths.update_width fixed K x other₁ other₁Width _ 0 zeroWidth
  have other₃Width : ∀ r, (other₃ r).size ≤ width :=
    GraphPackingWidths.update_width fixed K x other₂ other₂Width _ 0 zeroWidth
  have other₄Width : ∀ r, (other₄ r).size ≤ width :=
    GraphPackingWidths.update_width fixed K x other₃ other₃Width _ 0 zeroWidth
  have input₁Width : ∀ a, (input₁ a).size ≤ width :=
    GraphPackingWidths.update_width fixed K x advancedInput advancedInputWidth _ 0 zeroWidth
  have temporaryZero : initialOther (.inr Work.temporary) = 0 :=
    loaded_helper_zero fixed K x (x.graph.left e).val (x.graph.right e).val
      .temporary (Or.inr (Or.inr (Or.inl rfl)))
  have baseValue : initialOther (GraphPackingProgram.otherSetup fixed K .base) =
      GraphPackingPreparation.repetitions fixed K x + 1 := by
    change loadedOther fixed K x (x.graph.left e).val (x.graph.right e).val
      (.inl (PackingSetupMachine.output (parameters fixed K) .base)) = _
    rw [loaded_setup]
    rfl
  have edgeValue : initialInput .edgePower =
      (GraphPackingPreparation.repetitions fixed K x + 1) ^ e.val := by
    simp [initialInput, completedInputs, inputs]
  have productValue : PackingRegisterUpdate.operation .multiply
      (initialOther (GraphPackingProgram.otherSetup fixed K .base))
      (initialInput .edgePower) = nextPower := by
    simp only [PackingRegisterUpdate.operation, baseValue, edgeValue]
    exact (Nat.mul_comm _ _).trans (Nat.pow_succ _ _).symm
  obtain ⟨n₀, b₀, r₀⟩ := PackingVertexUpdate.general_exec
    (Numerator fixed) denominator .edgePower
    (GraphPackingProgram.otherSetup fixed K .base) (.inr Work.temporary)
    (by simp [GraphPackingProgram.otherSetup]) .multiply
    base initialInput initialOther temporaryZero state
  rw [productValue] at r₀
  change Exec (GraphPackingProgram.incrementEdge fixed K)
    ⟨state, tapes (Numerator fixed) denominator base initialInput initialOther⟩ n₀
    ⟨clean, tapes (Numerator fixed) denominator base advancedInput initialOther⟩ at r₀
  have multiplicationBound : n₀ ≤ 64 * (2 * width + 1) ^ 2 := by
    apply b₀.trans
    apply Nat.mul_le_mul_left 64
    apply Nat.pow_le_pow_left
    have hb := initialOtherWidth (GraphPackingProgram.otherSetup fixed K .base)
    have he := initialInputWidth .edgePower
    omega
  obtain ⟨n₁, b₁, r₁⟩ := PackingLayoutCommands.setOther_exec
    (Numerator fixed) denominator (.inr Work.leftEndpoint) 0
    base advancedInput initialOther clean width advancedInputWidth initialOtherWidth
  obtain ⟨n₂, b₂, r₂⟩ := PackingLayoutCommands.setOther_exec
    (Numerator fixed) denominator (.inr Work.rightEndpoint) 0
    base advancedInput other₁ clean width advancedInputWidth other₁Width
  obtain ⟨n₃, b₃, r₃⟩ := PackingLayoutCommands.setOther_exec
    (Numerator fixed) denominator (.inr Work.leftPower) 0
    base advancedInput other₂ clean width advancedInputWidth other₂Width
  obtain ⟨n₄, b₄, r₄⟩ := PackingLayoutCommands.setOther_exec
    (Numerator fixed) denominator (.inr Work.rightPower) 0
    base advancedInput other₃ clean width advancedInputWidth other₃Width
  obtain ⟨n₅, b₅, r₅⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .labelPower 0
    base advancedInput other₄ clean width advancedInputWidth other₄Width
  obtain ⟨n₆, b₆, r₆⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 0
    base input₁ other₄ clean width input₁Width other₄Width
  have finalOther : other₄ = preparedOther fixed K x :=
    clearedOther_eq fixed K x (x.graph.left e).val (x.graph.right e).val
  have finalInput : input₂ = inputs fixed K x (e.val + 1) :=
    clearedInputs_eq fixed K x e.val (x.graph.right e).val
  have runs := PhaseRuns.cons r₀ (PhaseRuns.cons r₁ (PhaseRuns.cons r₂
    (PhaseRuns.cons r₃ (PhaseRuns.cons r₄ (PhaseRuns.cons r₅ (PhaseRuns.single r₆))))))
  refine ⟨n₀ + (n₁ + (n₂ + (n₃ + (n₄ + (n₅ + n₆))))), ?_, ?_⟩
  · rw [cleanupTimePolynomial, Polynomial.eval_comp]
    change _ ≤ (cleanupWidthTimePolynomial fixed K).eval width
    simp only [cleanupWidthTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
    omega
  · change PhaseRuns (cleanupPhases fixed K)
      ⟨state, tapes (Numerator fixed) denominator base initialInput initialOther⟩ _
      ⟨clean, tapes (Numerator fixed) denominator base
        (inputs fixed K x (e.val + 1)) (preparedOther fixed K x)⟩
    rw [← finalOther, ← finalInput]
    simpa only [cleanupPhases, GraphPackingProgram.setWork, GraphPackingProgram.setItem]
      using runs

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobEdge
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes values)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def repeatTimePolynomial : Polynomial Nat :=
  (repeatWidthPolynomial fixed K).comp (GraphPackingWidths.polynomial fixed K)

theorem repeatTimePolynomial_eval (x : GraphReductionInput) :
    (repeatTimePolynomial fixed K).eval (graphBits x).length =
      (repeatSetPolynomial fixed K).eval (GraphPackingWidths.width fixed K x) +
      40 * (GraphPackingWidths.width fixed K x + 1) ^ 3 + 1 +
      (repeatLoopPolynomial fixed K).eval (3 * GraphPackingWidths.width fixed K x + 2) := by
  simp [repeatTimePolynomial, repeatWidthPolynomial, GraphPackingWidths.width]

theorem repeat_exec (x : GraphReductionInput) (edge : x.graph.Edge)
    (base : Tape fixed K → List Bool) (state : State)
    (counterEmpty : base (.inr .repetitionCounter) = []) :
    ∃ steps ≤ (repeatTimePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (repeatPhases fixed K)
        ⟨state, tapes (Numerator fixed) denominator base (inputs fixed K x edge.val)
          (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ steps
        ⟨guardState none, tapes (Numerator fixed) denominator
          (outputTapes (.inr .reverseOutput) base (edgeWord fixed K x edge))
          (repeatFinalInputs fixed K x edge)
          (loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val)⟩ := by
  let width := GraphPackingWidths.width fixed K x
  let count := GraphPackingPreparation.repetitions fixed K x
  let other := loadedOther fixed K x (x.graph.left edge).val (x.graph.right edge).val
  let input := repeatInputs fixed K x edge.val
  let vals := values (Numerator fixed) denominator input other
  have inputWidth : ∀ a, (input a).size ≤ width :=
    repeatInputs_width fixed K x edge.val (Nat.le_of_lt edge.isLt)
  have otherWidth : ∀ r, (other r).size ≤ width :=
    loadedOther_width fixed K x _ _ (x.graph.left edge).isLt (x.graph.right edge).isLt
  have initialWidth : ∀ a, (inputs fixed K x edge.val a).size ≤ width :=
    inputs_width fixed K x edge.val (Nat.le_of_lt edge.isLt)
  obtain ⟨setSteps, setBound, setRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 1 base (inputs fixed K x edge.val)
    other state width initialWidth otherWidth
  have sourceValue : vals (countRegister fixed K (.output .repetitions)) = count :=
    loaded_repetitions fixed K x _ _
  have counterZero : vals (work fixed K .counter) = 0 :=
    loaded_helper_zero fixed K x _ _ .counter (Or.inl rfl)
  have oneZero : vals (work fixed K .one) = 0 :=
    loaded_helper_zero fixed K x _ _ .one (Or.inr (Or.inl rfl))
  have temporaryZero : vals (work fixed K .temporary) = 0 :=
    loaded_helper_zero fixed K x _ _ .temporary (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨tallySteps, tallyBound, tallyRun⟩ := GraphPackingTapeBlocks.tally_exec
    fixed K (.output .repetitions) .repetitionCounter base vals
    (.arithmetic (BinaryAddMachine.clean ())) counterZero oneZero temporaryZero
  rw [sourceValue] at tallyBound
  have tallyFrame : registerTapes (slots fixed K)
      (Function.update base (.inr .repetitionCounter)
        (List.replicate count true ++ base (.inr .repetitionCounter))) vals =
      counterTapes (.inr .repetitionCounter)
        (tapes (Numerator fixed) denominator base input other) count := by
    rw [counterEmpty, List.append_nil]
    exact RegisterFrameEmission.external_update (slots fixed K) base vals
      (.inr .repetitionCounter) (GraphPackingTapeBlocks.slots_outside fixed K .repetitionCounter)
      (List.replicate count true)
  rw [sourceValue, tallyFrame] at tallyRun
  have hone : other (GraphPackingProgram.otherSetup fixed K .one) = 1 :=
    loaded_one fixed K x _ _
  have htemp : other (.inr .temporary) = 0 := temporaryZero
  obtain ⟨loopSteps, loopBound, loopRun⟩ := PackingJobLoop.exec_polynomial
    (Numerator fixed) denominator (PackingInventoryDescriptors.jobDescriptors fixed)
    .labelPower .repetitionOne (by decide)
    (.inr Work.leftPower) (.inr Work.rightPower)
    (GraphPackingProgram.otherSetup fixed K .one) (.inr Work.temporary)
    (by simp [GraphPackingProgram.otherSetup]) .reverseOutput .repetitionCounter (by decide)
    base input other hone htemp count width width inputWidth otherWidth
    (.arithmetic (BinaryAddMachine.clean ()))
  have streamEq := repeatStream_eq fixed K x edge
  have inputEq := repeatIteration_eq fixed K x edge
  change PackingJobLoop.stream (Numerator fixed) denominator
      (PackingInventoryDescriptors.jobDescriptors fixed) input .labelPower .repetitionOne
      (other (.inr Work.leftPower)) (other (.inr Work.rightPower)) count =
    edgeWord fixed K x edge at streamEq
  change PackingJobLoop.iterationInput input .labelPower .repetitionOne
      (other (.inr Work.rightPower)) count = repeatFinalInputs fixed K x edge at inputEq
  rw [streamEq, inputEq] at loopRun
  have finalCounter : (tapes (Numerator fixed) denominator
      (outputTapes (.inr Extra.reverseOutput) base (edgeWord fixed K x edge))
      (repeatFinalInputs fixed K x edge) other) (.inr .repetitionCounter) = [] := by
    simp [outputTapes, counterEmpty]
  have cleared : counterTapes (.inr Extra.repetitionCounter)
      (tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base (edgeWord fixed K x edge))
        (repeatFinalInputs fixed K x edge) other) 0 =
      tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base (edgeWord fixed K x edge))
        (repeatFinalInputs fixed K x edge) other := by
    simp only [counterTapes, List.replicate_zero]
    rw [← finalCounter, Function.update_eq_self]
  rw [cleared] at loopRun
  have phases : PhaseRuns (repeatPhases fixed K)
      ⟨state, tapes (Numerator fixed) denominator base (inputs fixed K x edge.val) other⟩
      (setSteps + (tallySteps + loopSteps))
      ⟨guardState none, tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base (edgeWord fixed K x edge))
        (repeatFinalInputs fixed K x edge) other⟩ :=
    .cons setRun (.cons tallyRun (PhaseRuns.single loopRun))
  refine ⟨setSteps + (tallySteps + loopSteps), ?_, phases⟩
  have hc : count ≤ width := Nat.le_trans (Nat.le_succ count)
    (GraphPackingWidths.repetitions_width fixed K x)
  have tallyUpper := repeat_tally_bound count width hc
  have aggregate : PackingJobLoop.aggregateWidth width width count ≤ 3 * width + 2 := by
    unfold PackingJobLoop.aggregateWidth
    omega
  have loopUpper := MachineComposition.natPolynomial_eval_mono
    (repeatLoopPolynomial fixed K) aggregate
  change loopSteps ≤ (repeatLoopPolynomial fixed K).eval
    (PackingJobLoop.aggregateWidth width width count) at loopBound
  change setSteps ≤ (repeatSetPolynomial fixed K).eval width at setBound
  rw [repeatTimePolynomial_eval]
  change setSteps + (tallySteps + loopSteps) ≤
    (repeatSetPolynomial fixed K).eval width + 40 * (width + 1) ^ 3 + 1 +
      (repeatLoopPolynomial fixed K).eval (3 * width + 2)
  omega

end

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

def edgeTimePolynomial : Polynomial Nat :=
  prefixTimePolynomial + repeatTimePolynomial fixed K + cleanupTimePolynomial fixed K + 1

theorem edge_exec (x : GraphReductionInput) (e : x.graph.Edge)
    (base : Tape fixed K → List Bool) (state : State) (suffix : List Bool)
    (sourceWord : base (.inr .endpoints) = true ::
      (BinaryEncoding.natBits (x.graph.left e).val ++
        (BinaryEncoding.natBits (x.graph.right e).val ++ suffix)))
    (decodeEmpty : base (.inr .decodeScratch) = [])
    (powerEmpty : base (.inr .powerCounter) = [])
    (repeatEmpty : base (.inr .repetitionCounter) = []) :
    ∃ steps ≤ (edgeTimePolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.edgeBody fixed K)
        ⟨state, tapes (Numerator fixed) denominator base (inputs fixed K x e.val)
          (preparedOther fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (resultBase fixed K base suffix (edgeWord fixed K x e))
            (inputs fixed K x (e.val + 1)) (preparedOther fixed K x)⟩ := by
  let decodedBase := Function.update base (.inr Extra.endpoints) suffix
  obtain ⟨n₁, b₁, r₁⟩ := prefix_exec fixed K x e base (inputs fixed K x e.val)
    suffix state sourceWord decodeEmpty powerEmpty
  have decodedRepeatEmpty : decodedBase (.inr .repetitionCounter) = [] := by
    simpa [decodedBase] using repeatEmpty
  obtain ⟨n₂, b₂, r₂⟩ := repeat_exec fixed K x e decodedBase
    (.arithmetic (BinaryAddMachine.clean ())) decodedRepeatEmpty
  obtain ⟨n₃, b₃, r₃⟩ := cleanup_exec fixed K x e
    (outputTapes (.inr .reverseOutput) decodedBase (edgeWord fixed K x e))
    (PackingCountedProgram.guardState none)
  have runs := (r₁.append r₂).append r₃
  refine ⟨(n₁ + n₂) + n₃ + 1, ?_, ?_⟩
  · simp only [edgeTimePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    omega
  · simpa only [GraphPackingProgram.edgeBody, prefixPhases, repeatPhases, cleanupPhases,
      List.cons_append, List.nil_append, decodedBase, resultBase, repeatFinalInputs]
      using runs.toExec

end BinPackingGap.GraphPackingJobs

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingGlobalExecution
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open GraphPackingPoolExec (layout_counter)

variable (fixed : InventoryData) (K : Nat)

theorem loop_exec_list (x : GraphReductionInput) (es : List x.graph.Edge)
    (base : Tape fixed K → List Bool) (start : Nat) (state : State)
    (indices : es.map Fin.val = List.range' start es.length)
    (sourceWord : base (.inr .endpoints) = edgeFields x es)
    (decodeEmpty : base (.inr .decodeScratch) = [])
    (powerEmpty : base (.inr .powerCounter) = [])
    (repeatEmpty : base (.inr .repetitionCounter) = []) :
    ∃ steps ≤ es.length * ((edgeTimePolynomial fixed K).eval (graphBits x).length + 1) + 1,
      Exec (PackingCountedProgram.loop (.inr .edgeCounter) (GraphPackingProgram.edgeBody fixed K))
        ⟨state, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator base (inputs fixed K x start)
            (preparedOther fixed K x)) es.length⟩ steps
        ⟨guardState none, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator
            (resultBase fixed K base [false] (edgeWords fixed K x es))
            (inputs fixed K x (start + es.length)) (preparedOther fixed K x)) 0⟩ := by
  induction es generalizing base start state with
  | nil =>
      have endpointNil : base (.inr .endpoints) = [false] := by
        simpa [edgeFields, BinaryEncoding.listBits] using sourceWord
      refine ⟨1, by simp, ?_⟩
      have stop : PackingCountedProgram.more
          ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
            ⟨state, counterTapes (.inr .edgeCounter)
              (tapes (Numerator fixed) denominator base (inputs fixed K x start)
                (preparedOther fixed K x)) 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        edgeWords, List.flatMap_nil, List.length_nil, Nat.add_zero,
        resultBase_nil fixed K base endpointNil] using
        (Exec.loop_false (a := GraphPackingProgram.edgeBody fixed K) stop)
  | cons e es ih =>
      obtain ⟨headIndex, tailIndices⟩ := contiguous_cons e es start indices
      let currentBase := counterTapes (.inr Extra.edgeCounter) base es.length
      let middleBase := resultBase fixed K base (edgeFields x es) (edgeWord fixed K x e)
      have currentWord : currentBase (.inr .endpoints) = true ::
          (BinaryEncoding.natBits (x.graph.left e).val ++
            (BinaryEncoding.natBits (x.graph.right e).val ++ edgeFields x es)) := by
        simpa [currentBase, counterTapes, edgeFields, BinaryEncoding.listBits,
          List.append_assoc] using sourceWord
      have currentDecode : currentBase (.inr .decodeScratch) = [] := by
        simpa [currentBase, counterTapes] using decodeEmpty
      have currentPower : currentBase (.inr .powerCounter) = [] := by
        simpa [currentBase, counterTapes] using powerEmpty
      have currentRepeat : currentBase (.inr .repetitionCounter) = [] := by
        simpa [currentBase, counterTapes] using repeatEmpty
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ := edge_exec fixed K x e currentBase
        (guardState (some true)) (edgeFields x es) currentWord currentDecode
        currentPower currentRepeat
      have bodyRun' : Exec (GraphPackingProgram.edgeBody fixed K)
          ⟨guardState (some true), counterTapes (.inr .edgeCounter)
            (tapes (Numerator fixed) denominator base (inputs fixed K x start)
              (preparedOther fixed K x)) es.length⟩ bodySteps
          ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
            (tapes (Numerator fixed) denominator middleBase (inputs fixed K x (start + 1))
              (preparedOther fixed K x)) es.length⟩ := by
        simpa only [currentBase, middleBase, headIndex, resultBase_counter,
          ← layout_counter] using bodyRun
      have middleWord : middleBase (.inr .endpoints) = edgeFields x es := by
        simp [middleBase]
      have middleDecode : middleBase (.inr .decodeScratch) = [] := by
        simpa [middleBase] using decodeEmpty
      have middlePower : middleBase (.inr .powerCounter) = [] := by
        simpa [middleBase] using powerEmpty
      have middleRepeat : middleBase (.inr .repetitionCounter) = [] := by
        simpa [middleBase] using repeatEmpty
      obtain ⟨tailSteps, tailBound, tailRun⟩ := ih middleBase (start + 1)
        (.arithmetic (BinaryAddMachine.clean ())) tailIndices middleWord
        middleDecode middlePower middleRepeat
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · simp only [List.length_cons, Nat.succ_mul]
        omega
      · have more : PackingCountedProgram.more
            ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
              ⟨state, counterTapes (.inr .edgeCounter)
                (tapes (Numerator fixed) denominator base (inputs fixed K x start)
                  (preparedOther fixed K x)) (es.length + 1)⟩).state = true := by
          rw [PackingCountedProgram.guard_succ]
          rfl
        have bodyAfterGuard : Exec (GraphPackingProgram.edgeBody fixed K)
            ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
              ⟨state, counterTapes (.inr .edgeCounter)
                (tapes (Numerator fixed) denominator base (inputs fixed K x start)
                  (preparedOther fixed K x)) (es.length + 1)⟩) bodySteps
            ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
              (tapes (Numerator fixed) denominator middleBase (inputs fixed K x (start + 1))
                (preparedOther fixed K x)) es.length⟩ := by
          rw [PackingCountedProgram.guard_succ]
          exact bodyRun'
        have combined := Exec.loop_true more bodyAfterGuard tailRun
        simpa only [PackingCountedProgram.loop, middleBase, resultBase_append,
          edgeWords, List.flatMap_cons, List.length_cons, Nat.add_assoc, Nat.add_comm 1 es.length]
          using combined

def loopTimePolynomial : Polynomial Nat :=
  Polynomial.X * (edgeTimePolynomial fixed K + 1) + 1

theorem loop_exec (x : GraphReductionInput) (base : Tape fixed K → List Bool)
    (state : State)
    (sourceWord : base (.inr .endpoints) = GraphFieldMachine.fieldBits .endpoints x)
    (decodeEmpty : base (.inr .decodeScratch) = [])
    (powerEmpty : base (.inr .powerCounter) = [])
    (repeatEmpty : base (.inr .repetitionCounter) = []) :
    ∃ steps ≤ (loopTimePolynomial fixed K).eval (graphBits x).length,
      Exec (PackingCountedProgram.loop (.inr .edgeCounter) (GraphPackingProgram.edgeBody fixed K))
        ⟨state, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator base (inputs fixed K x 0)
            (preparedOther fixed K x)) x.graph.edges.length⟩ steps
        ⟨guardState none, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator
            (resultBase fixed K base [false]
              (PackingDescriptorExpression.rawRecords
                (PackingInventoryDescriptors.jobStream (inventory fixed K x))))
            (inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)) 0⟩ := by
  obtain ⟨steps, bound, run⟩ := loop_exec_list fixed K x
    (List.finRange x.graph.edges.length) base 0 state
    (by simpa only [List.length_finRange] using contiguous_finRange x.graph.edges.length)
    (by simpa only [edgeFields_finRange] using sourceWord) decodeEmpty powerEmpty repeatEmpty
  refine ⟨steps, ?_, ?_⟩
  · have hm := graph_edgeCount_le_bits x
    have upper := Nat.mul_le_mul_right
      ((edgeTimePolynomial fixed K).eval (graphBits x).length + 1) hm
    simp only [List.length_finRange] at bound
    simp only [loopTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one]
    omega
  · simpa only [List.length_finRange, Nat.zero_add, edgeWords_finRange] using run

end BinPackingGap.GraphPackingJobs

namespace BinPackingGap.GraphPackingGlobalSemantics

open GraphPackingRegisters GraphPackingPreparation
open PackingDescriptorExpression PackingInventoryDescriptors GraphPackingStockStreams
open GraphPackingPoolExec GraphPackingGlobalPhases
open PackingItemExpression (Variable denominator)

variable (fixed : InventoryData) (K : Nat)

theorem prepared_globalStock (x : GraphReductionInput) (species : GlobalSpecies x.graph) :
    preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K (globalOutput species)) =
      (inventory fixed K x).globalStock species := by
  rw [prepared_output]
  cases species with
  | up one => cases one <;> rfl
  | um one => cases one <;> rfl
  | edge edge permit => rfl

theorem edgeInput_values (x : GraphReductionInput) (label : Option x.graph.Vertex)
    (oldEdge rep edge : Nat) :
    GraphPackingGlobalLoop.edgeInput fixed K
      (values (inventory fixed K x) label oldEdge rep) (preparedOther fixed K x) edge =
      values (inventory fixed K x) label edge rep := by
  funext vinput
  cases vinput <;>
    simp [GraphPackingGlobalLoop.edgeInput, prepared_radix, values]

theorem poolWord_global (x : GraphReductionInput) (species : GlobalSpecies x.graph) :
    poolWord fixed K (globalOutput species) (globalDescriptor (inventory fixed K x) species)
      (values (inventory fixed K x) none (globalEdgeIndex (inventory fixed K x) species) 0)
      (preparedOther fixed K x) =
      rawRecords (globalPoolStream (inventory fixed K x) species) := by
  unfold poolWord
  rw [prepared_globalStock]
  have hnum : numerator (inventory fixed K x) = numerator fixed := by
    funext descriptor
    exact numerator_instantiate fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k descriptor
  have records := globalPool_chunk_records (inventory fixed K x) species
  rw [hnum] at records
  simpa only [Numerator, inventory, instantiate] using records

theorem unitPools_word (x : GraphReductionInput) :
    poolListWord fixed K (unitPools fixed) (values (inventory fixed K x) none 0 0)
      (preparedOther fixed K x) =
      rawRecords (globalPoolStream (inventory fixed K x) (.up true) ++
        globalPoolStream (inventory fixed K x) (.up false) ++
        globalPoolStream (inventory fixed K x) (.um true) ++
        globalPoolStream (inventory fixed K x) (.um false)) := by
  have upOne := poolWord_global fixed K x (.up true)
  have upZero := poolWord_global fixed K x (.up false)
  have umOne := poolWord_global fixed K x (.um true)
  have umZero := poolWord_global fixed K x (.um false)
  dsimp only [globalOutput, globalDescriptor, globalEdgeIndex] at upOne upZero umOne umZero
  have words := congrArg₂ (fun a b : List Bool => a ++ b) upOne
    (congrArg₂ (fun a b : List Bool => a ++ b) upZero
      (congrArg₂ (fun a b : List Bool => a ++ b) umOne umZero))
  simpa only [poolListWord, unitPools, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    rawRecords, List.flatMap_append, List.append_assoc, inventory, instantiate] using words

theorem edgeWord_values (x : GraphReductionInput) (edge : x.graph.Edge) :
    GraphPackingGlobalLoop.edgeWord fixed K
      (values (inventory fixed K x) none edge.val 0) (preparedOther fixed K x) =
      rawRecords (globalPoolStream (inventory fixed K x) (.edge edge true) ++
        globalPoolStream (inventory fixed K x) (.edge edge false)) := by
  have yes := poolWord_global fixed K x (.edge edge true)
  have no := poolWord_global fixed K x (.edge edge false)
  dsimp only [globalOutput, globalDescriptor, globalEdgeIndex] at yes no
  simpa only [GraphPackingGlobalLoop.edgeWord, rawRecords, List.flatMap_append,
    inventory, instantiate] using
    congrArg₂ (fun a b : List Bool => a ++ b) yes no

theorem globalsWord_eq (x : GraphReductionInput) :
    globalsWord fixed K (values (inventory fixed K x) none x.graph.edges.length 0)
      (preparedOther fixed K x) = rawRecords (globalStream (inventory fixed K x)) := by
  have unitValues := unitInput_values fixed K x none x.graph.edges.length 0
  have unitWords := unitPools_word fixed K x
  have edgeValues := edgeInput_values fixed K x none 0 0
  have edgeWords := edgeWord_values fixed K x
  dsimp only [inventory, instantiate] at unitValues unitWords edgeValues edgeWords ⊢
  unfold globalsWord
  rw [unitValues, unitWords, prepared_globalCount fixed K x,
    GraphPackingGlobalLoop.stream_eq_finRange]
  simp_rw [Nat.zero_add, edgeValues, edgeWords]
  simp only [globalStream, rawRecords, List.flatMap_append, List.flatMap_assoc,
    List.append_assoc]

theorem globalsInput_eq (x : GraphReductionInput) :
    globalsInput fixed K (values (inventory fixed K x) none x.graph.edges.length 0)
      (preparedOther fixed K x) =
      values (inventory fixed K x) none x.graph.edges.length 0 := by
  have unitValues := unitInput_values fixed K x none x.graph.edges.length 0
  have edgeValues := edgeInput_values fixed K x none 0 0 x.graph.edges.length
  dsimp only [inventory, instantiate] at unitValues edgeValues ⊢
  unfold globalsInput
  rw [unitValues, prepared_globalCount fixed K x]
  exact edgeValues

end BinPackingGap.GraphPackingGlobalSemantics

namespace BinPackingGap.GraphPackingGlobalRuntime

open GraphPackingRegisters GraphPackingPreparation GraphPackingGlobalPhases
open GraphPackingPoolRuntime
open PackingItemExpression (denominator)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

theorem radixWidth_le (x : GraphReductionInput) :
    (GraphPackingGlobalLoop.radix fixed K (preparedOther fixed K x)).size ≤
      (GraphPackingStockBounds.widthPolynomial fixed K).eval (graphBits x).length :=
  GraphPackingStockBounds.preparedOther_size_le_polynomial fixed K x
    (GraphPackingProgram.otherSetup fixed K .base)

theorem aggregateWidth_le (x : GraphReductionInput) :
    GraphPackingGlobalLoop.aggregateWidth fixed K (preparedOther fixed K x)
      (GraphPackingWidths.width fixed K x + 1) 0
      (globalCount fixed K (preparedOther fixed K x)) ≤
      (edgeWidthPolynomial fixed K).eval (graphBits x).length := by
  have hw := adjustedWidth_le fixed K x
  have hm := Nat.mul_le_mul (graph_edgeCount_le_bits x) (radixWidth_le fixed K x)
  rw [GraphPackingGlobalLoop.aggregateWidth, GraphPackingGlobalSemantics.prepared_globalCount]
  simp only [Nat.zero_add, edgeWidthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

theorem bodyBudget_le (x : GraphReductionInput) (width : Nat)
    (hw : width ≤ (edgeWidthPolynomial fixed K).eval (graphBits x).length) :
    GraphPackingGlobalLoop.bodyBudget fixed K (preparedOther fixed K x) width ≤
      (edgeBodyPolynomial fixed K).eval (graphBits x).length := by
  have hc := stockCount_le fixed K x .edgeStock (by simp)
  have h₁ := poolBudget_le fixed K .edgeStock (.w, .globalEdge true)
    (preparedOther fixed K x) width (GraphPackingStockBounds.stockPolynomial fixed K)
    (edgeWidthPolynomial fixed K) (graphBits x).length hc hw
  have h₂ := poolBudget_le fixed K .edgeStock (.w, .globalEdge false)
    (preparedOther fixed K x) width (GraphPackingStockBounds.stockPolynomial fixed K)
    (edgeWidthPolynomial fixed K) (graphBits x).length hc hw
  have hsquare := Nat.pow_le_pow_left
    (Nat.add_le_add_right (Nat.add_le_add (radixWidth_le fixed K x) hw) 1) 2
  have hmul := Nat.mul_le_mul_left 64 hsquare
  simp only [GraphPackingGlobalLoop.bodyBudget, edgeBodyPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one]
  omega

theorem globalsBudget_le (x : GraphReductionInput) :
    globalsBudget fixed K (preparedOther fixed K x) (GraphPackingWidths.width fixed K x) ≤
      (globalsPolynomial fixed K).eval (graphBits x).length := by
  have hr := resetBudget_le fixed K x
  have hp := poolListBudget_le fixed K (unitPools fixed) (preparedOther fixed K x)
    (GraphPackingWidths.width fixed K x + 1) (GraphPackingStockBounds.stockPolynomial fixed K)
    (adjustedWidthPolynomial fixed K) (graphBits x).length
    (unitCounts_le fixed K x) (adjustedWidth_le fixed K x)
  have hc : globalCount fixed K (preparedOther fixed K x) ≤ (graphBits x).length := by
    rw [GraphPackingGlobalSemantics.prepared_globalCount]
    exact graph_edgeCount_le_bits x
  have ht := tally_le (globalCount fixed K (preparedOther fixed K x))
    (graphBits x).length Polynomial.X (by simpa only [Polynomial.eval_X] using hc)
  have hb := bodyBudget_le fixed K x _ (aggregateWidth_le fixed K x)
  have hl := Nat.mul_le_mul hc (Nat.add_le_add_right hb 1)
  simp only [globalsBudget, globalsPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  omega

end BinPackingGap.GraphPackingGlobalRuntime

namespace BinPackingGap.GraphPackingGlobalExecution

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters GraphPackingPreparation
open PackingItemExpression (denominator)
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

theorem globals_exec (x : GraphReductionInput)
    (base : GraphPackingRegisters.Tape fixed K → List Bool) (state : State)
    (poolEmpty : base (.inr .poolCounter) = [])
    (edgeEmpty : base (.inr .edgeCounter) = []) :
    ∃ steps ≤ (GraphPackingGlobalRuntime.globalsPolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.globals fixed K)
        ⟨state, tapes (Numerator fixed) denominator base
          (GraphPackingJobs.inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base
              (PackingDescriptorExpression.rawRecords
                (PackingInventoryDescriptors.globalStream (GraphPackingJobs.inventory fixed K x))))
            (GraphPackingJobs.inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)⟩ := by
  have counterZero : preparedOther fixed K x (.inr .counter) = 0 := rfl
  have oneZero : preparedOther fixed K x (.inr .one) = 0 := rfl
  have temporaryZero : preparedOther fixed K x (.inr .temporary) = 0 := rfl
  obtain ⟨steps, bound, run⟩ := GraphPackingGlobalPhases.globals_exec fixed K base
    (PackingDescriptorExpression.values (GraphPackingGlobalSemantics.inventory fixed K x)
      none x.graph.edges.length 0) (preparedOther fixed K x) state
    (GraphPackingWidths.width fixed K x) counterZero oneZero temporaryZero poolEmpty edgeEmpty
    (GraphPackingStockBounds.values_width fixed K x x.graph.edges.length le_rfl)
    (GraphPackingWidths.preparedOther_width fixed K x)
  refine ⟨steps, bound.trans (GraphPackingGlobalRuntime.globalsBudget_le fixed K x), ?_⟩
  rw [GraphPackingGlobalSemantics.globalsWord_eq,
    GraphPackingGlobalSemantics.globalsInput_eq] at run
  simpa only [GraphPackingJobs.inputs_eq_values, GraphPackingJobs.inventory,
    GraphPackingGlobalSemantics.inventory, PackingDescriptorExpression.instantiate] using run

theorem flags_exec (x : GraphReductionInput)
    (base : GraphPackingRegisters.Tape fixed K → List Bool) (state : State)
    (poolEmpty : base (.inr .poolCounter) = []) :
    ∃ steps ≤ (GraphPackingGlobalRuntime.flagsPolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.flags fixed K)
        ⟨state, tapes (Numerator fixed) denominator base
          (GraphPackingJobs.inputs fixed K x x.graph.edges.length) (preparedOther fixed K x)⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base
              (PackingDescriptorExpression.rawRecords
                (PackingInventoryDescriptors.flagStream (GraphPackingJobs.inventory fixed K x))))
            (GraphPackingJobs.inputs fixed K x 0) (preparedOther fixed K x)⟩ := by
  have counterZero : preparedOther fixed K x (.inr .counter) = 0 := rfl
  have oneZero : preparedOther fixed K x (.inr .one) = 0 := rfl
  have temporaryZero : preparedOther fixed K x (.inr .temporary) = 0 := rfl
  obtain ⟨steps, bound, run⟩ := GraphPackingGlobalPhases.flags_exec fixed K base
    (PackingDescriptorExpression.values (GraphPackingGlobalSemantics.inventory fixed K x)
      none x.graph.edges.length 0) (preparedOther fixed K x) state
    (GraphPackingWidths.width fixed K x) counterZero oneZero temporaryZero poolEmpty
    (GraphPackingStockBounds.values_width fixed K x x.graph.edges.length le_rfl)
    (GraphPackingWidths.preparedOther_width fixed K x)
  refine ⟨steps, bound.trans (GraphPackingGlobalRuntime.flagsBudget_le fixed K x), ?_⟩
  rw [GraphPackingGlobalSemantics.flagsWord_eq, GraphPackingGlobalSemantics.flagInput_eq] at run
  simpa only [GraphPackingJobs.inputs_eq_values, GraphPackingJobs.inventory,
    GraphPackingGlobalSemantics.inventory, PackingDescriptorExpression.instantiate] using run

end BinPackingGap.GraphPackingGlobalExecution

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingPreparation
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingPreparation

section

open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def powerPolynomial : Polynomial Nat :=
  80 * (Polynomial.X + 1) ^ 3 +
    2 * BinaryPowerMachine.timePolynomial.comp (2 * GraphPackingWidths.polynomial fixed K) + 4

theorem powerBudget_le (x : GraphReductionInput) :
    powerBudget fixed K x ≤ (powerPolynomial fixed K).eval (graphBits x).length := by
  let w := GraphPackingWidths.width fixed K x
  have ns : x.graph.n ≤ (graphBits x).length := graph_vertexCount_le_bits x
  have ms : x.graph.edges.length ≤ (graphBits x).length := graph_edgeCount_le_bits x
  have sw : (graphBits x).length + 1 ≤ w := GraphPackingWidths.input_length_le_width fixed K x
  have three : (3 : Nat).size ≤ w :=
    (nat_size_le_self 3).trans (GraphPackingWidths.small_constant_width fixed K x)
  have radix : (repetitions fixed K x + 1).size ≤ w :=
    (nat_size_le_self _).trans (GraphPackingWidths.repetitions_width fixed K x)
  have vertex := MachineComposition.natPolynomial_eval_mono BinaryPowerMachine.timePolynomial
    (show (3 : Nat).size + x.graph.n ≤ 2 * w by omega)
  have edge := MachineComposition.natPolynomial_eval_mono BinaryPowerMachine.timePolynomial
    (show (repetitions fixed K x + 1).size + x.graph.edges.length ≤ 2 * w by omega)
  have tn := tally_bound ns
  have tm := tally_bound ms
  simp only [powerPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_comp]
  change _ ≤ 80 * ((graphBits x).length + 1) ^ 3 +
    2 * BinaryPowerMachine.timePolynomial.eval (2 * w) + 4
  unfold powerBudget PackingPowerProgram.budget
  omega

def arithmeticPolynomial : Polynomial Nat :=
  PackingSetupMachine.timePolynomial (GraphPackingRegisters.parameters fixed K) +
    powerPolynomial fixed K + 1

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

variable (fixed : InventoryData) (K : Nat)

def timePolynomial : Polynomial Nat :=
  parsePolynomial fixed K + arithmeticPolynomial fixed K + finishPolynomial fixed K + 1

theorem prepare_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (timePolynomial fixed K).eval (graphBits x).length,
      Exec (prepare fixed K) ⟨state, initialTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), preparedTapes fixed K x⟩ := by
  obtain ⟨a, ha, arun⟩ := parse_exec fixed K x state
  obtain ⟨b, hb, brun⟩ := setup_exec fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨c, hc, crun⟩ := powers_exec fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨d, hd, drun⟩ := finish_exec fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  have middle := PhaseRuns.cons brun crun
  have whole := arun.append (middle.append drun)
  have actual := whole.toExec
  refine ⟨a + (b + c + d) + 1, ?_, ?_⟩
  · have powers := powerBudget_le fixed K x
    simp only [timePolynomial, arithmeticPolynomial, Polynomial.eval_add,
      Polynomial.eval_one] at ⊢
    omega
  · simpa only [prepare, parsePhases, powerPhases, List.cons_append, List.nil_append] using actual

end BinPackingGap.GraphPackingPreparation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingVerticesBound
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingVertices

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters PackingItemExpression
open GraphPackingProgram (PhaseRuns)

variable (fixed : InventoryData) (K : Nat)

theorem setup_exec (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (GraphPackingPreparation.preparedInputs fixed K x a).size ≤ width)
    (ho : ∀ a, (GraphPackingPreparation.preparedOther fixed K x a).size ≤ width)
    (state : State) :
    ∃ steps ≤ setupBound fixed K x width,
      PhaseRuns (setupPhases fixed K)
        ⟨state, GraphPackingPreparation.preparedTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), startTapes fixed K x⟩ := by
  let initial := GraphPackingPreparation.preparedInputs fixed K x
  let firstInput := Function.update initial .labelPower 3
  let secondInput := Function.update firstInput .edgePower 1
  have initialWidth : ∀ a, (initial a).size ≤ width + 2 := by
    intro a
    exact (hi a).trans (by omega)
  have otherWidth : ∀ a,
      (GraphPackingPreparation.preparedOther fixed K x a).size ≤ width + 2 := by
    intro a
    exact (ho a).trans (by omega)
  have threeSize : (3 : Nat).size = 2 := by decide
  have oneSize : (1 : Nat).size = 1 := by decide
  have firstWidth : ∀ a, (firstInput a).size ≤ width + 2 :=
    update_width initial .labelPower 3 (width + 2) initialWidth (by omega)
  have secondWidth : ∀ a, (secondInput a).size ≤ width + 2 :=
    update_width firstInput .edgePower 1 (width + 2) firstWidth (by omega)
  obtain ⟨firstSteps, firstBound, firstRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .labelPower 3 (startBase fixed K x) initial
    (GraphPackingPreparation.preparedOther fixed K x) state (width + 2)
    initialWidth otherWidth
  obtain ⟨secondSteps, secondBound, secondRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .edgePower 1 (startBase fixed K x) firstInput
    (GraphPackingPreparation.preparedOther fixed K x)
    (.arithmetic (BinaryAddMachine.clean ())) (width + 2) firstWidth otherWidth
  obtain ⟨thirdSteps, thirdBound, thirdRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 0 (startBase fixed K x) secondInput
    (GraphPackingPreparation.preparedOther fixed K x)
    (.arithmetic (BinaryAddMachine.clean ())) (width + 2) secondWidth otherWidth
  obtain ⟨tallySteps, tallyBound, tallyRun⟩ := GraphPackingTapeBlocks.tally_exec
    fixed K (.input .n) .vertexCounter (startBase fixed K x) (startValues fixed K x)
    (.arithmetic (BinaryAddMachine.clean ()))
    (startValues_counter fixed K x) (startValues_one fixed K x)
    (startValues_temporary fixed K x)
  rw [startValues_count_n] at tallyBound tallyRun
  rw [tally_frame] at tallyRun
  have phases : PhaseRuns (setupPhases fixed K)
      ⟨state, GraphPackingPreparation.preparedTapes fixed K x⟩
      (firstSteps + (secondSteps + (thirdSteps + tallySteps)))
      ⟨.arithmetic (BinaryAddMachine.clean ()), startTapes fixed K x⟩ :=
    .cons firstRun (.cons secondRun (.cons thirdRun (PhaseRuns.single tallyRun)))
  refine ⟨firstSteps + (secondSteps + (thirdSteps + tallySteps)), ?_, phases⟩
  unfold setupBound
  omega

end

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open FiniteTapeProgram PackingMachineBlocks
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

theorem exec (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (preparedInputs fixed K x a).size ≤ width)
    (ho : ∀ a, (preparedOther fixed K x a).size ≤ width) (state : State) :
    ∃ steps ≤ phaseBudget fixed K x width,
      Exec (GraphPackingProgram.vertices fixed K)
        ⟨state, preparedTapes fixed K x⟩ steps
        ⟨PackingCountedProgram.guardState none, finalTapes fixed K x⟩ := by
  obtain ⟨setupSteps, setupBound, setupRun⟩ := setup_exec fixed K x width hi ho state
  obtain ⟨loopSteps, loopBound, loopRun⟩ := loop_exec fixed K x width hi
  have runs := setupRun.append (GraphPackingProgram.PhaseRuns.single loopRun)
  refine ⟨setupSteps + loopSteps + 1, ?_, ?_⟩
  · unfold phaseBudget
    omega
  · simpa only [GraphPackingProgram.vertices, setupPhases, List.cons_append, List.nil_append]
      using runs.toExec

end BinPackingGap.GraphPackingVertices

namespace BinPackingGap.GraphPackingVerticesBound

open FiniteTapeProgram PackingMachineBlocks
open GraphPackingRegisters PackingItemExpression
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def polynomial : Polynomial Nat :=
  (setPolynomial fixed K).comp (GraphPackingWidths.polynomial fixed K + 2) +
    40 * (Polynomial.X + 1) ^ 3 + 1 +
    Polynomial.X *
      ((bodyPolynomial fixed).comp
        (GraphPackingWidths.polynomial fixed K + 2 * Polynomial.X + 5) + 1) + 1 + 1

theorem polynomial_eval (size : Nat) :
    (polynomial fixed K).eval size =
      (setPolynomial fixed K).eval ((GraphPackingWidths.polynomial fixed K).eval size + 2) +
        40 * (size + 1) ^ 3 + 1 +
        size * ((bodyPolynomial fixed).eval
          ((GraphPackingWidths.polynomial fixed K).eval size + 2 * size + 5) + 1) + 1 + 1 := by
  simp [polynomial]

theorem phaseBudget_le (x : GraphReductionInput) :
    GraphPackingVertices.phaseBudget fixed K x (GraphPackingWidths.width fixed K x) ≤
      (polynomial fixed K).eval (graphBits x).length := by
  let size := (graphBits x).length
  let width := GraphPackingWidths.width fixed K x
  have hn : x.graph.n ≤ size := graph_vertexCount_le_bits x
  have tally := tallyBound_le x.graph.n size hn
  have setup : GraphPackingVertices.setupBound fixed K x width ≤
      (setPolynomial fixed K).eval (width + 2) + 40 * (size + 1) ^ 3 + 1 := by
    simp only [GraphPackingVertices.setupBound, setPolynomial, Polynomial.eval_add]
    omega
  have aggregate : PackingVertexLoop.aggregateWidth (width + 2) 0 x.graph.n ≤
      width + 2 * size + 5 := by
    unfold PackingVertexLoop.aggregateWidth
    omega
  have body := MachineComposition.natPolynomial_eval_mono (bodyPolynomial fixed) aggregate
  have product := Nat.mul_le_mul hn (Nat.add_le_add_right body 1)
  have loop : GraphPackingVertices.loopBudget fixed K x width ≤
      size * ((bodyPolynomial fixed).eval (width + 2 * size + 5) + 1) + 1 := by
    simpa only [GraphPackingVertices.loopBudget, bodyPolynomial] using
      Nat.add_le_add_right product 1
  rw [polynomial_eval]
  change GraphPackingVertices.setupBound fixed K x width +
      GraphPackingVertices.loopBudget fixed K x width + 1 ≤
    (setPolynomial fixed K).eval (width + 2) + 40 * (size + 1) ^ 3 + 1 +
      size * ((bodyPolynomial fixed).eval (width + 2 * size + 5) + 1) + 1 + 1
  omega

theorem exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (polynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.vertices fixed K)
        ⟨state, GraphPackingPreparation.preparedTapes fixed K x⟩ steps
        ⟨PackingCountedProgram.guardState none, GraphPackingVertices.finalTapes fixed K x⟩ := by
  obtain ⟨steps, bound, run⟩ := GraphPackingVertices.exec fixed K x
    (GraphPackingWidths.width fixed K x)
    (GraphPackingWidths.preparedInputs_width fixed K x)
    (GraphPackingWidths.preparedOther_width fixed K x) state
  exact ⟨steps, bound.trans (phaseBudget_le fixed K x), run⟩

end BinPackingGap.GraphPackingVerticesBound

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingJobs

section

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram
open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)

variable (fixed : InventoryData) (K : Nat)

theorem vertexFinalInputs_width (x : GraphReductionInput) :
    ∀ a, (GraphPackingVertices.finalInputs fixed K x a).size ≤
      GraphPackingWidths.width fixed K x + 2 := by
  have original := GraphPackingVertices.inputValues_width fixed K x
    (GraphPackingWidths.width fixed K x) (GraphPackingWidths.preparedInputs_width fixed K x)
  intro a
  by_cases ha : a = Variable.labelPower
  · subst a
    rw [GraphPackingVertices.final_labelPower]
    exact (GraphPackingWidths.vertex_power_width fixed K x (x.graph.n + 1) le_rfl).trans
      (by omega)
  · simpa only [GraphPackingVertices.finalInputs,
      PackingVertexLoop.vertexInput_other _ _ _ _ ha] using original a

def setupTimePolynomial : Polynomial Nat :=
  (setupSetPolynomial fixed K).comp (GraphPackingWidths.polynomial fixed K + 2) +
    40 * (Polynomial.X + 1) ^ 3 + 1

def setupBound (x : GraphReductionInput) : Nat :=
  (setupSetPolynomial fixed K).eval (GraphPackingWidths.width fixed K x + 2) +
    BinaryToTallyMachine.runtimeBound x.graph.edges.length + 1

theorem setupBound_le (x : GraphReductionInput) :
    setupBound fixed K x ≤ (setupTimePolynomial fixed K).eval (graphBits x).length := by
  let size := (graphBits x).length
  have hm : x.graph.edges.length ≤ size := graph_edgeCount_le_bits x
  have hs : x.graph.edges.length.size ≤ size :=
    (nat_size_le_self _).trans hm
  have tally : BinaryToTallyMachine.runtimeBound x.graph.edges.length ≤
      40 * (size + 1) ^ 3 := by
    calc
      BinaryToTallyMachine.runtimeBound x.graph.edges.length =
          40 * (x.graph.edges.length + 1) * (x.graph.edges.length.size + 1) ^ 2 := rfl
      _ ≤ 40 * (size + 1) * (size + 1) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 40 (Nat.add_le_add_right hm 1))
          (Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2)
      _ = 40 * (size + 1) ^ 3 := by ring
  dsimp [size] at tally
  simp only [setupBound, setupTimePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, GraphPackingWidths.width]
  omega

theorem setup_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (setupTimePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (setupPhases fixed K)
        ⟨state, GraphPackingVertices.finalTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), setupTapes fixed K x⟩ := by
  let initial := GraphPackingVertices.finalInputs fixed K x
  let firstInput := Function.update initial .edgePower 1
  let secondInput := Function.update firstInput .labelPower 0
  let width := GraphPackingWidths.width fixed K x + 2
  have initialWidth : ∀ a, (initial a).size ≤ width := vertexFinalInputs_width fixed K x
  have otherWidth : ∀ a, (preparedOther fixed K x a).size ≤ width := by
    intro a
    exact (GraphPackingWidths.preparedOther_width fixed K x a).trans (by omega)
  have oneSize : (1 : Nat).size = 1 := by decide
  have zeroSize : (0 : Nat).size = 0 := by decide
  have firstWidth : ∀ a, (firstInput a).size ≤ width :=
    bounded_update initial .edgePower 1 width initialWidth (by dsimp [width]; omega)
  have secondWidth : ∀ a, (secondInput a).size ≤ width :=
    bounded_update firstInput .labelPower 0 width firstWidth (by dsimp [width]; omega)
  obtain ⟨firstSteps, firstBound, firstRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .edgePower 1 (GraphPackingVertices.finalBase fixed K x)
    initial (preparedOther fixed K x) state width initialWidth otherWidth
  obtain ⟨secondSteps, secondBound, secondRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .labelPower 0 (GraphPackingVertices.finalBase fixed K x)
    firstInput (preparedOther fixed K x) (.arithmetic (BinaryAddMachine.clean ()))
    width firstWidth otherWidth
  obtain ⟨thirdSteps, thirdBound, thirdRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 0 (GraphPackingVertices.finalBase fixed K x)
    secondInput (preparedOther fixed K x) (.arithmetic (BinaryAddMachine.clean ()))
    width secondWidth otherWidth
  have thirdInput : Function.update secondInput .repetitionOne 0 = inputs fixed K x 0 :=
    resetInputs_eq fixed K x
  rw [thirdInput] at thirdRun
  obtain ⟨tallySteps, tallyBound, tallyRun⟩ := GraphPackingTapeBlocks.tally_exec
    fixed K (.input .m) .edgeCounter (GraphPackingVertices.finalBase fixed K x)
    (setupValues fixed K x) (.arithmetic (BinaryAddMachine.clean ())) rfl rfl rfl
  have count : setupValues fixed K x (countRegister fixed K (.input .m)) =
      x.graph.edges.length := rfl
  rw [count] at tallyBound tallyRun
  rw [tally_frame] at tallyRun
  have phases : PhaseRuns (setupPhases fixed K)
      ⟨state, GraphPackingVertices.finalTapes fixed K x⟩
      (firstSteps + (secondSteps + (thirdSteps + tallySteps)))
      ⟨.arithmetic (BinaryAddMachine.clean ()), setupTapes fixed K x⟩ := by
    rw [GraphPackingVertices.finalTapes_eq_frame]
    exact .cons firstRun (.cons secondRun (.cons thirdRun (PhaseRuns.single tallyRun)))
  refine ⟨firstSteps + (secondSteps + (thirdSteps + tallySteps)),
    le_trans ?_ (setupBound_le fixed K x), phases⟩
  dsimp [width] at firstBound secondBound thirdBound
  simp only [setupBound, setupSetPolynomial, Polynomial.eval_add]
  omega

end

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

def timePolynomial : Polynomial Nat :=
  setupTimePolynomial fixed K + loopTimePolynomial fixed K + 1

theorem exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (timePolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.jobs fixed K)
        ⟨state, GraphPackingVertices.finalTapes fixed K x⟩ steps
        ⟨guardState none, finalTapes fixed K x⟩ := by
  obtain ⟨setupSteps, setupBound, setupRun⟩ := setup_exec fixed K x state
  have sourceWord : GraphPackingVertices.finalBase fixed K x (.inr .endpoints) =
      GraphFieldMachine.fieldBits .endpoints x := by
    simp [GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
      PackingItemBlockMachine.outputTapes, baseTapes]
  have decodeEmpty : GraphPackingVertices.finalBase fixed K x (.inr .decodeScratch) = [] := by
    simp [GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
      PackingItemBlockMachine.outputTapes, baseTapes]
  have powerEmpty : GraphPackingVertices.finalBase fixed K x (.inr .powerCounter) = [] := by
    simp [GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
      PackingItemBlockMachine.outputTapes, baseTapes]
  have repeatEmpty : GraphPackingVertices.finalBase fixed K x (.inr .repetitionCounter) = [] := by
    simp [GraphPackingVertices.finalBase, GraphPackingVertices.startBase,
      PackingItemBlockMachine.outputTapes, baseTapes]
  obtain ⟨loopSteps, loopBound, loopRun⟩ := loop_exec fixed K x
    (GraphPackingVertices.finalBase fixed K x) (.arithmetic (BinaryAddMachine.clean ()))
    sourceWord decodeEmpty powerEmpty repeatEmpty
  have finalEmpty : finalTapes fixed K x (.inr .edgeCounter) = [] := by
    simp [finalTapes]
  have cleared : counterTapes (.inr Extra.edgeCounter) (finalTapes fixed K x) 0 =
      finalTapes fixed K x := by
    simp only [counterTapes, List.replicate_zero]
    rw [← finalEmpty, Function.update_eq_self]
  change Exec _ _ loopSteps
    ⟨guardState none, counterTapes (.inr .edgeCounter) (finalTapes fixed K x) 0⟩ at loopRun
  rw [cleared] at loopRun
  have runs := setupRun.append (PhaseRuns.single loopRun)
  refine ⟨setupSteps + loopSteps + 1, ?_, ?_⟩
  · simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one]
    omega
  · simpa only [GraphPackingProgram.jobs, setupPhases, List.cons_append, List.nil_append]
      using runs.toExec

end BinPackingGap.GraphPackingJobs

namespace BinPackingGap.GraphPackingRun

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open GraphPackingPreparation PackingItemExpression
open GraphPackingProgram (PhaseRuns)
open PackingMachineLayout (tapes)
open PackingItemBlockMachine (outputTapes)
open PackingDescriptorExpression (rawRecords)
open PackingInventoryDescriptors

variable (fixed : InventoryData) (K : Nat)

def prefixTimePolynomial : Polynomial Nat :=
  GraphPackingPreparation.timePolynomial fixed K +
    GraphPackingVerticesBound.polynomial fixed K + GraphPackingJobs.timePolynomial fixed K +
    GraphPackingGlobalRuntime.globalsPolynomial fixed K + GraphPackingGlobalRuntime.flagsPolynomial fixed K

theorem prefix_runs (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (prefixTimePolynomial fixed K).eval (graphBits x).length,
      PhaseRuns (prefixPhases fixed K)
        ⟨state, initialTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), beforeFinishTapes fixed K x⟩ := by
  obtain ⟨n₁, b₁, r₁⟩ := GraphPackingPreparation.prepare_exec fixed K x state
  obtain ⟨n₂, b₂, r₂⟩ := GraphPackingVerticesBound.exec fixed K x
    (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨n₃, b₃, r₃⟩ := GraphPackingJobs.exec fixed K x (PackingCountedProgram.guardState none)
  have jobPoolEmpty : GraphPackingJobs.finalBase fixed K x (.inr .poolCounter) = [] := by simp
  have jobEdgeEmpty : GraphPackingJobs.finalBase fixed K x (.inr .edgeCounter) = [] := by simp
  obtain ⟨n₄, b₄, r₄⟩ := GraphPackingGlobalExecution.globals_exec fixed K x
    (GraphPackingJobs.finalBase fixed K x) (PackingCountedProgram.guardState none)
    jobPoolEmpty jobEdgeEmpty
  have globalPoolEmpty : afterGlobalBase fixed K x (.inr .poolCounter) = [] := by
    simp [afterGlobalBase, outputTapes]
  obtain ⟨n₅, b₅, r₅⟩ := GraphPackingGlobalExecution.flags_exec fixed K x
    (afterGlobalBase fixed K x) (.arithmetic (BinaryAddMachine.clean ())) globalPoolEmpty
  have runs := PhaseRuns.cons r₁ (PhaseRuns.cons r₂
    (PhaseRuns.cons r₃ (PhaseRuns.cons r₄ (PhaseRuns.single r₅))))
  refine ⟨n₁ + (n₂ + (n₃ + (n₄ + n₅))), ?_, runs⟩
  simp only [prefixTimePolynomial, Polynomial.eval_add]
  omega

def wordTimePolynomial : Polynomial Nat :=
  (prefixTimePolynomial fixed K + 1) * Polynomial.C (prefixPushBound fixed K)

theorem constructorWord_length_le (x : GraphReductionInput) :
    (constructorWord fixed K x).length ≤
      (wordTimePolynomial fixed K).eval (graphBits x).length := by
  obtain ⟨steps, bound, runs⟩ := prefix_runs fixed K x (.arithmetic (BinaryAddMachine.clean ()))
  have run : Exec (prefixProgram fixed K)
      ⟨.arithmetic (BinaryAddMachine.clean ()), initialTapes fixed K x⟩ (steps + 1)
      ⟨.arithmetic (BinaryAddMachine.clean ()), beforeFinishTapes fixed K x⟩ := runs.toExec
  have lengthBound := run.stack_length_le (.inr .input) (.inr .output)
    (.arithmetic (BinaryAddMachine.clean ())) (.inr .reverseOutput)
  change (beforeFinishTapes fixed K x (.inr .reverseOutput)).length ≤
    (initialTapes fixed K x (.inr .reverseOutput)).length +
      (steps + 1) * prefixPushBound fixed K at lengthBound
  rw [beforeFinish_reverse, List.length_reverse] at lengthBound
  have initialEmpty : initialTapes fixed K x (.inr .reverseOutput) = [] := rfl
  rw [initialEmpty, List.length_nil, Nat.zero_add] at lengthBound
  have times := Nat.mul_le_mul_right (prefixPushBound fixed K) (Nat.add_le_add_right bound 1)
  simp only [wordTimePolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_C]
  exact lengthBound.trans times

def timePolynomial : Polynomial Nat :=
  prefixTimePolynomial fixed K + wordTimePolynomial fixed K + 6

theorem exec (x : GraphReductionInput) :
    ∃ steps ≤ (timePolynomial fixed K).eval (graphBits x).length,
      Exec (GraphPackingProgram.code fixed K)
        ⟨.arithmetic (BinaryAddMachine.clean ()), initialTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()), finalTapes fixed K x⟩ := by
  obtain ⟨prefixSteps, prefixBound, prefixRun⟩ := prefix_runs fixed K x
    (.arithmetic (BinaryAddMachine.clean ()))
  have finishRun := GraphPackingFinish.finish_exec fixed K (beforeFinishTapes fixed K x)
    (.arithmetic (BinaryAddMachine.clean ())) (constructorWord fixed K x)
    (beforeFinish_reverse fixed K x) (beforeFinish_output_empty fixed K x)
  have allRuns := prefixRun.append (PhaseRuns.single finishRun)
  refine ⟨prefixSteps + ((constructorWord fixed K x).length + 5) + 1, ?_, ?_⟩
  · have wordBound := constructorWord_length_le fixed K x
    simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_ofNat]
    omega
  · simpa only [GraphPackingProgram.code, prefixPhases, List.cons_append, List.nil_append,
      finalTapes] using allRuns.toExec

def terminalRun (x : GraphReductionInput) :
    MachineCanonicalOutput.TerminalRun (GraphPackingFinish.rawProgram fixed K)
      (graphBits x)
      (BinaryEncoding.rawReductionOutputBits (GraphPackingJobs.inventory fixed K x).rawOutput)
      ((timePolynomial fixed K).eval (graphBits x).length) := by
  classical
  let steps := Classical.choose (exec fixed K x)
  have bound := (Classical.choose_spec (exec fixed K x)).1
  have run := (Classical.choose_spec (exec fixed K x)).2
  refine {
    state := .arithmetic (BinaryAddMachine.clean ())
    tapes := finalTapes fixed K x
    execution := {
      steps := steps
      evals_in_steps := ?_
      steps_le_m := bound }
    output_eq := ?_ }
  · have initialEq : initList
        (MachineCanonicalOutput.sourceMachine (GraphPackingFinish.rawProgram fixed K)) (graphBits x) =
        (⟨some (GraphPackingProgram.code fixed K).entry,
          .arithmetic (BinaryAddMachine.clean ()), initialTapes fixed K x⟩ :
          (MachineCanonicalOutput.sourceMachine (GraphPackingFinish.rawProgram fixed K)).Cfg) := by
      unfold initList
      dsimp only [MachineCanonicalOutput.sourceMachine, GraphPackingFinish.rawProgram]
      congr 1
      funext tape
      cases tape with
      | inl tape => simp [initialTapes]
      | inr extra =>
          cases extra <;> simp [initialTapes]
          rfl
    change (MachineComposition.advance
      (TM2.step ((GraphPackingProgram.code fixed K).instruction id none)))^[steps]
      (some (initList
        (MachineCanonicalOutput.sourceMachine (GraphPackingFinish.rawProgram fixed K)) (graphBits x))) =
      some ⟨none, .arithmetic (BinaryAddMachine.clean ()), finalTapes fixed K x⟩
    rw [initialEq]
    exact run.trace ((GraphPackingProgram.code fixed K).instruction id none) id none (fun _ => rfl)
  · change finalTapes fixed K x (.inr .output) = _
    rw [finalTapes, GraphPackingFinish.resultTapes_output, constructorWord_eq]

end BinPackingGap.GraphPackingRun

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

def graphPackingComputation (c : Nat) (ρ : ℝ) :
    TM2ComputableInPolyTime graphBits BinaryEncoding.rawReductionOutputBits
      (graphPackingOutput c ρ) :=
  MachineCanonicalOutput.computableInPolyTime
    (GraphPackingFinish.rawProgram (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c))
    (GraphPackingFinish.cleanupTapes (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c))
    (GraphPackingFinish.cleanup_complete (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c))
    graphBits BinaryEncoding.rawReductionOutputBits (graphPackingOutput c ρ)
    (GraphPackingRun.timePolynomial (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c))
    (fun x => by
      simpa only [GraphPackingFixedParameters.rawOutput_eq] using
        GraphPackingRun.terminalRun (GraphPackingFixedParameters.fixedInventory c ρ) (lossAllowance c) x)

end BinPackingGap

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchUpdateMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open SearchSemantics SearchEncoding BinaryEncoding

def fillSteps (s : State) : Nat :=
  fillPrefixSteps s + ((fixedBits s.fixed).length + (s.item + 1) + (natBits s.label).length) +
    ((fillBody s).length + 2)

theorem fillTrace (s : State) :
    (advance machine.step)^[fillSteps s]
      (some (cfg (some .fillYesBins) (ambient .fill)
        (work (bodyBits s) [] [] [] [] [] [] []))) =
      some (cfg none (ambient (fillPhase s))
        (work [] [] (fillCounter s).1 [] [] [] [] (phaseBits (fillPhase s) ++ fillBody s))) := by
  have first := fillPrefixTrace s
  have second := replaceTrace (ambient (fillPhase s)) s.fixed s.item s.label
    (fillCounter s).1 ((rawInstanceBits s.items).reverse ++ (fillHeader s).reverse)
  have third := reverseFinishTrace (ambient (fillPhase s)) [] [] (fillCounter s).1 [] [] []
    ((fixedBits (newFixed s)).reverse ++ (rawInstanceBits s.items).reverse ++ (fillHeader s).reverse)
  simp only [newFixed, List.append_assoc] at third
  have full := joinTrace (joinTrace first second) third
  simpa [fillSteps, fillBody, newFixed, List.reverse_append, List.reverse_reverse,
    List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

theorem fillBudget_le (s : State) :
    1 + fillSteps s ≤ rawTime.eval ((stateBits s).length + 1) := by
  have lengths := stateBits_length s
  have convert := UnaryToBinaryMachine.steps_le s.label 0
  have fixed := fixedBits_set_length_le s.fixed s.item s.label
  have width : s.label.size ≤ s.label := Nat.size_le.mpr s.label.lt_two_pow_self
  have labelBound : s.label ≤ (stateBits s).length := label_le_stateBits_length s
  have square := Nat.mul_le_mul labelBound labelBound
  simp only [Nat.zero_add] at convert
  simp only [fillSteps, fillPrefixSteps, fillBody, fillHeader, newFixed,
    List.length_append, List.length_cons, List.length_nil, encodeWord_length,
    natBits_length, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  rw [Nat.size_eq_bits_len]
  nlinarith

def rawRun (p : State × Bool) :
    MachineCanonicalOutput.TerminalRun program
      (MachineKeepDecision.typedOutputBits stateBits p)
      (stateBits (SearchMachineComposition.applyAnswer p))
      (rawTime.eval (MachineKeepDecision.typedOutputBits stateBits p).length) := by
  rcases p with ⟨s, answer⟩
  change MachineCanonicalOutput.TerminalRun program (answer :: stateBits s)
    (stateBits (update s answer)) (rawTime.eval (answer :: stateBits s).length)
  have start := startStep s.phase answer (bodyBits s)
  rw [← stateBits_eq] at start
  cases phase : s.phase with
  | done =>
      refine copyRun s answer (ambient .done answer) [] (by simp) ?_ ?_
      · simpa [initialTarget, phase] using start
      · simp [update, phase, stateBits_eq]
  | invalid =>
      refine copyRun s answer (ambient .invalid answer) [] (by simp) ?_ ?_
      · simpa [initialTarget, phase] using start
      · simp [update, phase, stateBits_eq]
  | find =>
      cases answer with
      | false =>
          refine copyRun s false (ambient .find) [true] (by simp) ?_ ?_
          · simpa [initialTarget, phase] using start
          · simp [update, phase, stateBits, phaseBits, bodyBits, encodeWord,
              List.replicate_succ, List.append_assoc]
      | true =>
          refine {
            state := (ambient .fill, none)
            tapes := work [] [] [] [] [] [] [] (phaseBits .fill ++ findBody s)
            execution := {
              steps := 1 + findSteps s
              evals_in_steps := ?_
              steps_le_m := by simpa using findBudget_le s }
            output_eq := ?_ }
          · rw [init_eq]
            change (advance machine.step)^[1 + findSteps s] _ = _
            have first := by simpa only [initialTarget, phase] using start
            exact joinTrace (oneStepTrace first) (findTrace s)
          · simp [program, work, update, phase, stateBits, findBody, encodeWord,
              List.append_assoc]
  | fill =>
      cases answer with
      | false =>
          refine {
            state := (ambient .fill, none)
            tapes := work [] [] [] [] [] [] [] (phaseBits .fill ++ fillNoBody s)
            execution := {
              steps := 1 + fillNoSteps s
              evals_in_steps := ?_
              steps_le_m := by simpa using fillNoBudget_le s }
            output_eq := ?_ }
          · rw [init_eq]
            change (advance machine.step)^[1 + fillNoSteps s] _ = _
            have first := by simpa only [initialTarget, phase] using start
            exact joinTrace (oneStepTrace first) (fillNoTrace s)
          · simp [program, work, update, phase, stateBits, fillNoBody, List.append_assoc]
      | true =>
          refine {
            state := (ambient (fillPhase s), none)
            tapes := work [] [] (fillCounter s).1 [] [] [] []
              (phaseBits (fillPhase s) ++ fillBody s)
            execution := {
              steps := 1 + fillSteps s
              evals_in_steps := ?_
              steps_le_m := by simpa using fillBudget_le s }
            output_eq := ?_ }
          · rw [init_eq]
            change (advance machine.step)^[1 + fillSteps s] _ = _
            have first := by simpa only [initialTarget, phase] using start
            exact joinTrace (oneStepTrace first) (fillTrace s)
          · simp [program, work, update, phase, stateBits, fillBody, fillHeader,
              fillPhase, newFixed, encodeWord, List.append_assoc]

noncomputable def computation :
    TM2ComputableInPolyTime (MachineKeepDecision.typedOutputBits stateBits) stateBits
      SearchMachineComposition.applyAnswer :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    (MachineKeepDecision.typedOutputBits stateBits) stateBits
    SearchMachineComposition.applyAnswer rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes cleanup_complete
    (MachineKeepDecision.typedOutputBits stateBits) stateBits
    SearchMachineComposition.applyAnswer rawTime rawRun

end BinPackingGap.SearchUpdateMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchStageMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchStageMachines

noncomputable def stages : SearchMachineComposition.Stages where
  initializeComputation := SearchInitializeMachine.computation
  initializeFinite := SearchInitializeMachine.finiteAlphabet
  prepareComputation := SearchPrepareMachine.computation
  prepareFinite := SearchPrepareMachine.finiteAlphabet
  updateComputation := SearchUpdateMachine.computation
  updateFinite := SearchUpdateMachine.finiteAlphabet
  finalizeComputation := SearchFinalizeMachine.computation
  finalizeFinite := SearchFinalizeMachine.finiteAlphabet

end BinPackingGap.SearchStageMachines

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Results_OptimalSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

noncomputable def absoluteAdditiveAlgorithm_of_pEqualsNP (h : PEqualsNP) :
    AbsoluteAdditiveAlgorithm 0 :=
  SearchOptimalConstruction.ofDecision SearchStageMachines.stages
    (OptimalSearch.decider h) (OptimalSearch.decisionComputation h)
    (OptimalSearch.decisionSpec h).1 (OptimalSearch.decidesExtension h)

@[simp] theorem absoluteAdditiveAlgorithm_of_pEqualsNP_empty (h : PEqualsNP) :
    (absoluteAdditiveAlgorithm_of_pEqualsNP h).run (BinaryEncoding.rawInstanceBits []) =
      some ⟨0, []⟩ :=
  SearchMachineComposition.algorithm_empty (OptimalSearch.decider h)

end BinPackingGap

end OAI
end


