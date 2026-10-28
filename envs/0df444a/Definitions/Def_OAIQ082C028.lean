-- Prove2me | Definitions.Def_OAIQ082C028
-- name    : OAIQ082C028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T14:39:33.831652+00:00
-- url     : https://prove2.me/theorems/f0c0f988-4a2c-4d54-866e-f009f9740ca2
-- title:
--   Definitions bundle OAIQ082C028 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 7 definitions and 26 theorems. The definitions and types are `OAI.BinPackingGap.SearchInitialEmitMachine.computation`, `OAI.BinPackingGap.SearchInitialEmitMachine.emitInTime`, `OAI.BinPackingGap.SearchInitialEmitMachine.fuelInTime`, `OAI.BinPackingGap.SearchInitialEmitMachine.rawRun`, `OAI.BinPackingGap.SearchInitializeMachine.composed`, `OAI.BinPackingGap.SearchInitializeMachine.computation`, `OAI.BinPackingGap.SearchUpdateMachine.copyRun`.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`BinPacking_Arithmetic_ResetExpressionCompiler`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Arithmetic/ResetExpressionCompiler.lean), [`BinPacking_Machines_GraphPackingGlobalExecution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingGlobalExecution.lean), [`BinPacking_Machines_GraphPackingPreparationFinish`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingPreparationFinish.lean), [`BinPacking_Machines_GraphPackingVerticesBound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingVerticesBound.lean), [`BinPacking_Machines_PackingJobLoop`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/PackingJobLoop.lean), [`BinPacking_Machines_PackingSetupGraph`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/PackingSetupGraph.lean), [`BinPacking_Search_SearchStageMachines`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchStageMachines.lean), [`BinPacking_Search_SearchUpdateMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchUpdateMachine.lean).
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C024`, `OAIQ082C025` and `OAIQ082C026` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ082C029`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C024
import Definitions.Def_OAIQ082C025
import Definitions.Def_OAIQ082C026

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_ResetExpressionCompiler
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeBEq _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.ResetExpressionCompiler

open NatExpressionCompiler BinaryRegisterProgram PairExpressionCompiler

variable {α Reg : Type} [DecidableEq Reg]

theorem correct (inputs : α → Reg) (expression : Expr α)
    (nodes : Node expression ↪ Reg) (apart : ∀ a n, inputs a ≠ nodes n)
    (output : Reg) (outputApart : ∀ n, output ≠ nodes n)
    (inputOutput : ∀ a, inputs a ≠ output)
    (values : Reg → Nat) (empty : ∀ n, values (nodes n) = 0) :
    Ready (commands inputs expression nodes apart output outputApart) values ∧
      resultOf (commands inputs expression nodes apart output outputApart) values =
        Function.update values output (eval (fun a => values (inputs a)) expression) := by
  let reset := result (.clear output) values
  let calculated := resultOf (compileInto inputs expression nodes apart) reset
  have resetNodes : ∀ n, reset (nodes n) = 0 := by
    intro n
    simp [reset, result, destination, value, Ne.symm (outputApart n), empty n]
  have resetInputs : ∀ a, reset (inputs a) = values (inputs a) := by
    intro a
    simp [reset, result, destination, value, inputOutput a]
  have compiled := compileInto_correct inputs expression nodes apart reset resetNodes
  have outputZero : calculated output = 0 := by
    rw [show calculated output = reset output from compiled.2.2 output outputApart]
    simp [reset, result, destination, value]
  have rootValue : calculated (nodes (root expression)) =
      eval (fun a => values (inputs a)) expression := by
    simpa only [calculated, resetInputs] using compiled.2.1
  constructor
  · change True ∧ Ready (compileInto inputs expression nodes apart ++ _) reset
    refine ⟨True.intro, ?_⟩
    rw [Ready_append]
    refine ⟨compiled.1, ?_⟩
    change calculated output = 0 ∧ _
    exact ⟨outputZero, clearList_ready _ _⟩
  · funext r
    simp only [commands, resultOf_cons, resultOf_append]
    rw [clearList_result]
    by_cases member : r ∈ nodeList expression nodes
    · obtain ⟨n, rfl⟩ := (mem_nodeList expression nodes r).mp member
      simp only [ite_eq_left member]
      simp [Ne.symm (outputApart n), empty n]
    · rw [ite_eq_right member]
      have outside : ∀ n, r ≠ nodes n := by
        intro n hn
        exact member ((mem_nodeList expression nodes r).mpr ⟨n, hn⟩)
      by_cases same : r = output
      · subst r
        simpa only [calculated, reset, result, destination, value, Function.update_self] using rootValue
      · have preserved : calculated r = reset r := compiled.2.2 r outside
        change (result (.copy output (nodes (root expression)) (outputApart _))
          calculated) r = Function.update values output _ r
        rw [result_other _ _ _ same, preserved]
        simp [reset, result, destination, value, same]

end BinPackingGap.ResetExpressionCompiler

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingJobLoop
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingJobBody

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

theorem chunk_exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (output : Extra) (base : Tape num den Other Extra → List Bool)
    (input : α → Nat) (other : Other → Nat) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (state : State) :
    ∃ steps ≤ (PackingChunkMachine.timePolynomial num den descriptors).eval width + 1,
      Exec (PackingArithmeticProgram.code
          (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors))
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den (outputTapes (.inr output) base
            (PackingChunkMachine.records num den (fun _ => input) descriptors)) input other⟩ := by
  have chunk := PackingChunkMachine.exec num den (itemSlots num den) (.inr output)
    (fun d => itemSlots_outside num den d output) descriptors
    (tapes num den base input other) (fun _ => input) () width
    (fun d _ => item_shape num den base input other d) (fun _ _ => hi)
  obtain ⟨steps, bound, run⟩ := PackingArithmeticProgram.exec_in_time
    (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors)
    _ _ _ state chunk
  rw [layout_output] at run
  exact ⟨steps, bound, run⟩

theorem body_exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (inputDifferent : power ≠ repetition)
    (leftPower rightPower one temp : Other) (different : one ≠ temp) (output : Extra)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat) (other : Other → Nat)
    (hone : other one = 1) (htemp : other temp = 0) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width)
    (state : State) :
    ∃ steps ≤ (bodyTimePolynomial num den descriptors power leftPower rightPower).eval width,
      Exec (body num den descriptors power repetition leftPower rightPower one temp different output)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den
            (outputTapes (.inr output) base
              (pairRecords num den descriptors input power (other leftPower) (other rightPower)))
            (nextInput input power repetition (other rightPower)) other⟩ := by
  let leftInput := Function.update input power (other leftPower)
  let rightInput := Function.update input power (other rightPower)
  let leftWord := PackingChunkMachine.records num den (fun _ => leftInput) descriptors
  let rightWord := PackingChunkMachine.records num den (fun _ => rightInput) descriptors
  have leftWidth : ∀ a, (leftInput a).size ≤ width :=
    update_size_le input power (other leftPower) width hi (ho leftPower)
  have rightWidth : ∀ a, (rightInput a).size ≤ width :=
    update_size_le input power (other rightPower) width hi (ho rightPower)
  obtain ⟨copyLeftSteps, copyLeftBound, copyLeftRun⟩ :=
    PackingLayoutCommands.inputFromOther_exec num den power leftPower base input other
      state width hi ho
  obtain ⟨emitLeftSteps, emitLeftBound, emitLeftRun⟩ :=
    chunk_exec num den descriptors output base leftInput other width leftWidth
      (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨copyRightSteps, copyRightBound, copyRightRun⟩ :=
    PackingLayoutCommands.inputFromOther_exec num den power rightPower
      (outputTapes (.inr output) base leftWord) leftInput other
      (.arithmetic (BinaryAddMachine.clean ())) width leftWidth ho
  simp only [leftInput, Function.update_idem] at copyRightRun
  obtain ⟨emitRightSteps, emitRightBound, emitRightRun⟩ :=
    chunk_exec num den descriptors output (outputTapes (.inr output) base leftWord)
      rightInput other width rightWidth (.arithmetic (BinaryAddMachine.clean ()))
  obtain ⟨updateSteps, updateBound, updateRun⟩ :=
    PackingVertexUpdate.general_exec num den repetition one temp different .add
      (outputTapes (.inr output) (outputTapes (.inr output) base leftWord) rightWord)
      rightInput other htemp (.arithmetic (BinaryAddMachine.clean ()))
  have next : Function.update rightInput repetition
      (PackingRegisterUpdate.operation .add (other one) (rightInput repetition)) =
      nextInput input power repetition (other rightPower) := by
    simp only [rightInput, PackingRegisterUpdate.operation, hone,
      Function.update_of_ne (Ne.symm inputDifferent), nextInput]
    exact congrArg
      (Function.update (Function.update input power (other rightPower)) repetition)
      (Nat.add_comm 1 (input repetition))
  rw [next] at updateRun
  refine ⟨copyLeftSteps + (emitLeftSteps + (copyRightSteps + (emitRightSteps + updateSteps))),
    ?_, ?_⟩
  · rw [bodyTimePolynomial_eval]
    have sizeOne : (1 : Nat).size = 1 := by decide
    rw [hone, sizeOne] at updateBound
    have hr := rightWidth repetition
    have square : (1 + (rightInput repetition).size + 1) ^ 2 ≤ (width + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) _
    have ub := updateBound.trans (Nat.mul_le_mul_left 64 square)
    omega
  · have combined := Exec.seq copyLeftRun
      (Exec.seq emitLeftRun (Exec.seq copyRightRun (Exec.seq emitRightRun updateRun)))
    simpa only [body, leftInput, rightInput, leftWord, rightWord, pairRecords,
      PackingChunkMachine.outputTapes_append] using combined

end BinPackingGap.PackingJobBody

namespace BinPackingGap.PackingJobLoop

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)
open PackingJobBody (nextInput pairRecords bodyTimePolynomial)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

theorem exec_bounded (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (inputDifferent : power ≠ repetition)
    (leftPower rightPower one temp : Other) (different : one ≠ temp)
    (output counter : Extra) (outputCounter : output ≠ counter)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hone : other one = 1) (htemp : other temp = 0)
    (count width : Nat) (state : State)
    (hi : ∀ r, r ≤ count → ∀ a,
      (iterationInput input power repetition (other rightPower) r a).size ≤ width)
    (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ count * ((bodyTimePolynomial num den descriptors power
        leftPower rightPower).eval width + 1) + 1,
      Exec (code num den descriptors power repetition inputDifferent leftPower rightPower
          one temp different output counter)
        ⟨state, counterTapes (.inr counter) (tapes num den base input other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power repetition
                (other leftPower) (other rightPower) count))
            (iterationInput input power repetition (other rightPower) count) other) 0⟩ := by
  induction count generalizing input base state with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      have stop : PackingCountedProgram.more ((PackingCountedProgram.guard (.inr counter)).eval
          ⟨state, counterTapes (.inr counter) (tapes num den base input other) 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [code, PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        stream, iterationInput, PackingChunkMachine.outputTapes_nil] using
        (Exec.loop_false (a := PackingJobBody.body num den descriptors power repetition
          leftPower rightPower one temp different output) stop)
  | succ count ih =>
      let word := pairRecords num den descriptors input power (other leftPower) (other rightPower)
      let next := nextInput input power repetition (other rightPower)
      have initialWidth : ∀ a, (input a).size ≤ width := hi 0 (by omega)
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ :=
        PackingJobBody.body_exec num den descriptors power repetition inputDifferent
          leftPower rightPower one temp different output
          (counterTapes (.inr counter) base count) input other hone htemp width
          initialWidth ho (guardState (some true))
      rw [layout_counter, output_counter num den base output counter outputCounter,
        layout_counter] at bodyRun
      have tailWidth : ∀ r, r ≤ count → ∀ a,
          (iterationInput next power repetition (other rightPower) r a).size ≤ width := by
        intro r hr
        rw [iterationInput_succ input power repetition (other rightPower) inputDifferent r]
        exact hi (r + 1) (by omega)
      obtain ⟨tailSteps, tailBound, tailRun⟩ :=
        ih (outputTapes (.inr output) base word) next
          (.arithmetic (BinaryAddMachine.clean ())) tailWidth
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · have more : PackingCountedProgram.more
            ((PackingCountedProgram.guard (.inr counter)).eval
              ⟨state, counterTapes (.inr counter) (tapes num den base input other)
                (count + 1)⟩).state = true := by
          rw [PackingCountedProgram.guard_succ]
          rfl
        have bodyRun' : Exec (PackingJobBody.body num den descriptors power repetition
            leftPower rightPower one temp different output)
            ((PackingCountedProgram.guard (.inr counter)).eval
              ⟨state, counterTapes (.inr counter) (tapes num den base input other)
                (count + 1)⟩) bodySteps
            ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr counter)
              (tapes num den (outputTapes (.inr output) base word) next other) count⟩ := by
          rw [PackingCountedProgram.guard_succ]
          exact bodyRun
        have combined := Exec.loop_true more bodyRun' tailRun
        simpa only [code, PackingCountedProgram.loop, next, word, stream,
          PackingChunkMachine.outputTapes_append,
          iterationInput_succ input power repetition (other rightPower) inputDifferent count]
          using combined

theorem exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (inputDifferent : power ≠ repetition)
    (leftPower rightPower one temp : Other) (different : one ≠ temp)
    (output counter : Extra) (outputCounter : output ≠ counter)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hone : other one = 1) (htemp : other temp = 0)
    (count inputWidth otherWidth : Nat)
    (hi : ∀ a, (input a).size ≤ inputWidth) (ho : ∀ a, (other a).size ≤ otherWidth)
    (state : State) :
    ∃ steps ≤ count * ((bodyTimePolynomial num den descriptors power
        leftPower rightPower).eval (aggregateWidth inputWidth otherWidth count) + 1) + 1,
      Exec (code num den descriptors power repetition inputDifferent leftPower rightPower
          one temp different output counter)
        ⟨state, counterTapes (.inr counter) (tapes num den base input other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power repetition
                (other leftPower) (other rightPower) count))
            (iterationInput input power repetition (other rightPower) count) other) 0⟩ := by
  apply exec_bounded num den descriptors power repetition inputDifferent
    leftPower rightPower one temp different output counter outputCounter base input other
    hone htemp count (aggregateWidth inputWidth otherWidth count) state
  · intro r hr
    exact iterationInput_size_le input power repetition (other rightPower) inputDifferent
      inputWidth otherWidth count r hr hi (ho rightPower)
  · intro a
    have h := ho a
    unfold aggregateWidth
    omega

theorem exec_polynomial (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power repetition : α) (inputDifferent : power ≠ repetition)
    (leftPower rightPower one temp : Other) (different : one ≠ temp)
    (output counter : Extra) (outputCounter : output ≠ counter)
    (base : Tape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hone : other one = 1) (htemp : other temp = 0)
    (count inputWidth otherWidth : Nat)
    (hi : ∀ a, (input a).size ≤ inputWidth) (ho : ∀ a, (other a).size ≤ otherWidth)
    (state : State) :
    ∃ steps ≤ (timePolynomial num den descriptors power leftPower rightPower).eval
        (aggregateWidth inputWidth otherWidth count),
      Exec (code num den descriptors power repetition inputDifferent leftPower rightPower
          one temp different output counter)
        ⟨state, counterTapes (.inr counter) (tapes num den base input other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power repetition
                (other leftPower) (other rightPower) count))
            (iterationInput input power repetition (other rightPower) count) other) 0⟩ := by
  obtain ⟨steps, bound, run⟩ := exec num den descriptors power repetition inputDifferent
    leftPower rightPower one temp different output counter outputCounter base input other
    hone htemp count inputWidth otherWidth hi ho state
  refine ⟨steps, bound.trans ?_, run⟩
  have hc : count ≤ aggregateWidth inputWidth otherWidth count := by
    unfold aggregateWidth
    omega
  simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one] using
    Nat.add_le_add_right (Nat.mul_le_mul_right
      ((bodyTimePolynomial num den descriptors power leftPower rightPower).eval
        (aggregateWidth inputWidth otherWidth count) + 1) hc) 1

end BinPackingGap.PackingJobLoop

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_PackingSetupGraph
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeBEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingSetupMachine

section

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram
open PackingSetupExpression

theorem block_correct (p : Parameters) (o : Output)
    (ins : Input → Nat) (outs : Output → Nat) :
    Ready (block p o) (frame p ins outs) ∧
      resultOf (block p o) (frame p ins outs) =
        frame p ins (Function.update outs o (eval ins (expression p o))) := by
  have h := ResetExpressionCompiler.correct (input p) (expression p o) (nodes p o)
    (by intros; simp [input, nodes]) (output p o) (by
      intro n equal
      change (Sum.inr (Sum.inl o) : Reg p) = Sum.inr (Sum.inr ⟨o, n⟩) at equal
      cases Sum.inr.inj equal)
    (by intros; simp [input, output]) (frame p ins outs) (fun _ => rfl)
  refine ⟨h.1, ?_⟩
  calc
    resultOf (block p o) (frame p ins outs) =
        Function.update (frame p ins outs) (output p o) (eval ins (expression p o)) := by
      simpa only [block, input, frame] using h.2
    _ = _ := frame_update p ins outs o _

theorem commandsFor_correct (p : Parameters) (order : List Output)
    (ins : Input → Nat) (outs : Output → Nat) :
    Ready (commandsFor p order) (frame p ins outs) ∧
      resultOf (commandsFor p order) (frame p ins outs) =
        frame p ins (outputsAfter p ins order outs) := by
  induction order generalizing outs with
  | nil => exact ⟨True.intro, rfl⟩
  | cons o tail ih =>
      have head := block_correct p o ins outs
      have rest := ih (Function.update outs o (eval ins (expression p o)))
      constructor
      · change Ready (block p o ++ commandsFor p tail) (frame p ins outs)
        rw [Ready_append, head.2]
        exact ⟨head.1, rest.1⟩
      · change resultOf (block p o ++ commandsFor p tail) (frame p ins outs) = _
        rw [resultOf_append, head.2]
        exact rest.2

theorem commands_correct (p : Parameters) (n m k : Nat) :
    Ready (commands p) (frame p (inputs n m k) (fun _ => 0)) ∧
      resultOf (commands p) (frame p (inputs n m k) (fun _ => 0)) =
        frame p (inputs n m k) (outputValues p n m k) := by
  have h := commandsFor_correct p outputOrder (inputs n m k) (fun _ => 0)
  refine ⟨h.1, h.2.trans ?_⟩
  congr 1
  funext o
  rw [outputsAfter_eq, ite_eq_left (mem_outputOrder o), eval_expression]

variable {K A : Type} [DecidableEq K]

theorem exec (p : Parameters) (slot : (Reg p ⊕ Fin 6) ↪ K)
    (base : K → List Bool) (n m k width : Nat)
    (hn : n.size ≤ width) (hm : m.size ≤ width) (hk : k.size ≤ width)
    (ambient : A) :
    ∃ steps ≤ (timePolynomial p).eval width,
      Exec (code p slot)
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base (frame p (inputs n m k) (fun _ => 0))⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base (frame p (inputs n m k) (outputValues p n m k))⟩ := by
  have hwidth : ∀ r, (frame p (inputs n m k) (fun _ => 0) r).size ≤ width := by
    intro r
    rcases r with a | (o | temp)
    · cases a
      · exact hn
      · exact hm
      · exact hk
    · simp [frame]
    · simp [frame]
  have correct := commands_correct p n m k
  obtain ⟨steps, bound, run⟩ := BinaryRegisterStructured.exec_polynomial slot (commands p)
    base (frame p (inputs n m k) (fun _ => 0)) correct.1 ambient width hwidth
  refine ⟨steps, ?_, ?_⟩
  · simpa only [timePolynomial, Polynomial.eval_add, Polynomial.eval_C] using bound
  · rw [correct.2] at run
    exact run

end

open BinaryRegisterProgram FiniteTapeProgram PackingSetupExpression

theorem exec_graph {K A : Type} [DecidableEq K]
    (p : Parameters) (slot : (Reg p ⊕ Fin 6) ↪ K) (base : K → List Bool)
    (x : GraphReductionInput) (ambient : A) :
    ∃ steps ≤ (timePolynomial p).eval (graphBits x).length,
      Exec (code p slot)
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base
            (frame p (inputs x.graph.n x.graph.edges.length x.k) (fun _ => 0))⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot base
            (frame p (inputs x.graph.n x.graph.edges.length x.k)
              (outputValues p x.graph.n x.graph.edges.length x.k))⟩ :=
  exec p slot base x.graph.n x.graph.edges.length x.k (graphBits x).length
    ((nat_size_le_self x.graph.n).trans (graph_vertexCount_le_bits x))
    ((nat_size_le_self x.graph.edges.length).trans (graph_edgeCount_le_bits x))
    ((nat_size_le_self x.k).trans (x.k_le.trans (graph_vertexCount_le_bits x))) ambient

end BinPackingGap.PackingSetupMachine

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

namespace BinPackingGap.PackingVertexLoop

open FiniteTapeProgram PackingMachineBlocks BinaryRegisterProgram NatExpressionCompiler
open PackingMachineLayout
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable {α δ Other Extra : Type}
variable [DecidableEq α] [DecidableEq δ] [DecidableEq Other] [DecidableEq Extra]

theorem body_exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output : Extra)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hthree : other three = 3) (htemp : other temp = 0)
    (vertex width : Nat) (hwidth : ∀ a, (vertexInput input power vertex a).size ≤ width)
    (state : State) :
    ∃ steps ≤ (bodyTimePolynomial num den descriptors).eval width,
      Exec (body num den descriptors power three temp different output)
        ⟨state, tapes num den base (vertexInput input power vertex) other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den
            (outputTapes (.inr output) base
              (PackingChunkMachine.records num den
                (fun _ => vertexInput input power vertex) descriptors))
            (vertexInput input power (vertex + 1)) other⟩ := by
  let word := PackingChunkMachine.records num den
    (fun _ => vertexInput input power vertex) descriptors
  have chunk := PackingChunkMachine.exec num den (itemSlots num den) (.inr output)
    (fun d => itemSlots_outside num den d output) descriptors
    (tapes num den base (vertexInput input power vertex) other)
    (fun _ => vertexInput input power vertex) () width
    (fun d _ => item_shape num den base (vertexInput input power vertex) other d)
    (fun _ _ => hwidth)
  obtain ⟨emitSteps, emitBound, emitRun⟩ := PackingArithmeticProgram.exec_in_time
    (PackingChunkMachine.code num den (itemSlots num den) (.inr output) descriptors)
    _ _ _ state chunk
  rw [layout_output] at emitRun
  obtain ⟨updateSteps, updateBound, updateRun⟩ :=
    PackingVertexUpdate.exec num den power three temp different
      (outputTapes (.inr output) base word) (vertexInput input power vertex) other
      hthree htemp (.arithmetic (BinaryAddMachine.clean ()))
  rw [vertexInput_update] at updateRun
  refine ⟨emitSteps + updateSteps, ?_, Exec.seq emitRun updateRun⟩
  rw [bodyTimePolynomial_eval]
  have hp := hwidth power
  have sizeThree : (3 : Nat).size = 2 := by decide
  rw [sizeThree] at updateBound
  have square : (2 + (vertexInput input power vertex power).size + 1) ^ 2 ≤
      (width + 3) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have ub := updateBound.trans (Nat.mul_le_mul_left 64 square)
  omega

theorem exec_bounded (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output counter : Extra)
    (outputCounter : output ≠ counter)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hthree : other three = 3) (htemp : other temp = 0)
    (start count width : Nat) (state : State)
    (hwidth : ∀ vertex, start ≤ vertex → vertex < start + count →
      ∀ a, (vertexInput input power vertex a).size ≤ width) :
    ∃ steps ≤ count * ((bodyTimePolynomial num den descriptors).eval width + 1) + 1,
      Exec (code num den descriptors power three temp different output counter)
        ⟨state, counterTapes (.inr counter)
          (tapes num den base (vertexInput input power start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power start count))
            (vertexInput input power (start + count)) other) 0⟩ := by
  induction count generalizing start base state with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      have stop : PackingCountedProgram.more ((PackingCountedProgram.guard (.inr counter)).eval
          ⟨state, counterTapes (.inr counter)
            (tapes num den base (vertexInput input power start) other) 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [code, PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        stream, PackingChunkMachine.outputTapes_nil, Nat.add_zero] using
        (Exec.loop_false (a := body num den descriptors power three temp different output) stop)
  | succ count ih =>
      let word := PackingChunkMachine.records num den
        (fun _ => vertexInput input power start) descriptors
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ := body_exec num den descriptors
        power three temp different output (counterTapes (.inr counter) base count)
        input other hthree htemp start width (hwidth start (by omega) (by omega))
        (guardState (some true))
      rw [layout_counter, output_counter num den base output counter outputCounter,
        layout_counter] at bodyRun
      obtain ⟨tailSteps, tailBound, tailRun⟩ := ih
        (outputTapes (.inr output) base word) (start + 1)
        (.arithmetic (BinaryAddMachine.clean ()))
        (fun vertex lower upper => hwidth vertex (by omega) (by omega))
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · have more : PackingCountedProgram.more
            ((PackingCountedProgram.guard (.inr counter)).eval
              ⟨state, counterTapes (.inr counter)
                (tapes num den base (vertexInput input power start) other) (count + 1)⟩).state = true := by
          rw [PackingCountedProgram.guard_succ]
          rfl
        have bodyRun' : Exec (body num den descriptors power three temp different output)
            ((PackingCountedProgram.guard (.inr counter)).eval
              ⟨state, counterTapes (.inr counter)
                (tapes num den base (vertexInput input power start) other) (count + 1)⟩) bodySteps
            ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr counter)
              (tapes num den (outputTapes (.inr output) base word)
                (vertexInput input power (start + 1)) other) count⟩ := by
          rw [PackingCountedProgram.guard_succ]
          exact bodyRun
        have combined := Exec.loop_true more bodyRun' tailRun
        simpa only [code, PackingCountedProgram.loop, word, stream,
          PackingChunkMachine.outputTapes_append, Nat.add_assoc, Nat.add_comm 1 count] using combined

theorem exec (num : δ → Expr α) (den : Expr α) (descriptors : List δ)
    (power : α) (three temp : Other) (different : three ≠ temp) (output counter : Extra)
    (outputCounter : output ≠ counter)
    (base : VertexTape num den Other Extra → List Bool) (input : α → Nat)
    (other : Other → Nat) (hthree : other three = 3) (htemp : other temp = 0)
    (start count inputWidth : Nat) (initial : ∀ a, (input a).size ≤ inputWidth)
    (state : State) :
    ∃ steps ≤ count * ((bodyTimePolynomial num den descriptors).eval
        (aggregateWidth inputWidth start count) + 1) + 1,
      Exec (code num den descriptors power three temp different output counter)
        ⟨state, counterTapes (.inr counter)
          (tapes num den base (vertexInput input power start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr counter)
          (tapes num den
            (outputTapes (.inr output) base
              (stream num den descriptors input power start count))
            (vertexInput input power (start + count)) other) 0⟩ := by
  exact exec_bounded num den descriptors power three temp different output counter
    outputCounter base input other hthree htemp start count
    (aggregateWidth inputWidth start count) state
    (fun vertex _ upper => vertexInput_size_le input power inputWidth start count vertex
      initial (Nat.le_of_lt upper))

end BinPackingGap.PackingVertexLoop

namespace BinPackingGap.GraphPackingPreparation

section

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram PackingRegisterFrame

variable (fixed : InventoryData) (K : Nat)

theorem setup_exec (x : GraphReductionInput) (state : State) :
    ∃ steps ≤ (PackingSetupMachine.timePolynomial (parameters fixed K)).eval (graphBits x).length + 1,
      Exec (PackingArithmeticProgram.code
        (PackingSetupMachine.code (parameters fixed K) (setupSlots fixed K)))
        ⟨state, parsedTapes fixed K x⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes (slots fixed K) (baseTapes fixed K x) (setupValues fixed K x)⟩ := by
  let before := PackingMachineLayout.values (Numerator fixed) PackingItemExpression.denominator
    (fun _ => 0) (parsedOther fixed K x)
  have inputFrame : registerTapes (setupSlots fixed K) (parsedTapes fixed K x)
      (PackingSetupMachine.frame (parameters fixed K)
        (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k) (fun _ => 0)) =
      parsedTapes fixed K x := by
    exact restrict (slots fixed K) (setup fixed K) (baseTapes fixed K x) before
  have outputFrame : registerTapes (setupSlots fixed K) (parsedTapes fixed K x)
      (PackingSetupMachine.frame (parameters fixed K)
        (PackingSetupExpression.inputs x.graph.n x.graph.edges.length x.k)
        (PackingSetupExpression.outputValues (parameters fixed K)
          x.graph.n x.graph.edges.length x.k)) =
      registerTapes (slots fixed K) (baseTapes fixed K x) (setupValues fixed K x) := by
    apply replace (slots fixed K) (setup fixed K) (baseTapes fixed K x)
      before (setupValues fixed K x)
    · intro r; rfl
    · intro r outside
      rcases r with (v | (r | w)) | node
      · rfl
      · exact False.elim (outside ⟨r, rfl⟩)
      · rfl
      · rfl
  obtain ⟨t, ht, run⟩ := PackingSetupMachine.exec_graph (parameters fixed K)
    (setupSlots fixed K) (parsedTapes fixed K x) x ()
  rw [inputFrame, outputFrame] at run
  exact PackingArithmeticProgram.exec_in_time _ _ _ _ state ⟨t, ht, run⟩

end

open GraphPackingRegisters BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open GraphPackingProgram

end BinPackingGap.GraphPackingPreparation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingGlobalExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingGlobalSemantics

open GraphPackingRegisters GraphPackingPreparation
open PackingDescriptorExpression PackingInventoryDescriptors GraphPackingStockStreams
open GraphPackingPoolExec GraphPackingGlobalPhases
open PackingItemExpression (Variable denominator)

variable (fixed : InventoryData) (K : Nat)

theorem unitInput_values (x : GraphReductionInput) (label : Option x.graph.Vertex)
    (edge rep : Nat) :
    unitInput (values (inventory fixed K x) label edge rep) =
      values (inventory fixed K x) none 0 0 := by
  funext vinput
  cases vinput <;> simp [unitInput, values, NaturalPackingNumerator.labelPower]

end BinPackingGap.GraphPackingGlobalSemantics

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

open GraphPackingRegisters GraphPackingPreparation PackingItemExpression
open FiniteTapeProgram PackingMachineBlocks
open PackingItemBlockMachine (outputTapes)

variable (fixed : InventoryData) (K : Nat)

theorem loop_exec (x : GraphReductionInput) (width : Nat)
    (hi : ∀ a, (preparedInputs fixed K x a).size ≤ width) :
    ∃ steps ≤ loopBudget fixed K x width,
      Exec (PackingVertexLoop.code (Numerator fixed) denominator
        (PackingInventoryDescriptors.vertexDescriptors fixed) .labelPower
        (GraphPackingProgram.otherSetup fixed K .three) (.inr Work.temporary)
        (by simp [GraphPackingProgram.otherSetup]) .reverseOutput .vertexCounter)
        ⟨.arithmetic (BinaryAddMachine.clean ()), startTapes fixed K x⟩ steps
        ⟨PackingCountedProgram.guardState none, finalTapes fixed K x⟩ := by
  have hthree : preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K .three) = 3 := rfl
  have htemp : preparedOther fixed K x (.inr Work.temporary) = 0 := rfl
  have run := PackingVertexLoop.exec (Numerator fixed) denominator
    (PackingInventoryDescriptors.vertexDescriptors fixed) .labelPower
    (GraphPackingProgram.otherSetup fixed K .three) (.inr Work.temporary)
    (by simp [GraphPackingProgram.otherSetup]) .reverseOutput .vertexCounter (by decide)
    (startBase fixed K x) (inputValues fixed K x) (preparedOther fixed K x) hthree htemp
    0 x.graph.n (width + 2) (inputValues_width fixed K x width hi)
    (.arithmetic (BinaryAddMachine.clean ()))
  simpa only [loopBudget, startTapes, startInputs_eq, stream_eq_emitted,
    finalTapes, finalBase, finalInputs, Nat.zero_add] using run

end BinPackingGap.GraphPackingVertices

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

theorem unarySkipStep (current next : Label) (atLabel : code current = skipUnary current next)
    (bit : Bool) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    machine.step (cfg (some current) phase (io base (bit :: input) reversed)) =
      some (cfg (some (if bit then current else next)) phase (io base input reversed)) := by
  change some (TM2.stepAux (code current) _ _) = _
  rw [atLabel]
  cases bit <;> simp [skipUnary, go, TM2.stepAux, cfg, update_io_input]
  all_goals rfl

theorem unarySkipTrace (current next : Label) (atLabel : code current = skipUnary current next)
    (n : Nat) (phase : Ambient) (base : Tapes) (input reversed : List Bool) :
    (advance machine.step)^[n + 1]
      (some (cfg (some current) phase (io base (encodeWord n ++ input) reversed))) =
      some (cfg (some next) phase (io base input reversed)) := by
  induction n with
  | zero =>
      simpa [encodeWord, advance] using! unarySkipStep current next atLabel
        false phase base input reversed
  | succ n ih =>
      have first := unarySkipStep current next atLabel true phase base
        (encodeWord n ++ input) reversed
      have full := joinTrace (oneStepTrace first) ih
      simpa [encodeWord, List.replicate_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using full

theorem startStep (phase : Phase) (answer : Bool) (body : List Bool) :
    machine.step (cfg (some .start) (ambient .find)
      (work (answer :: (phaseBits phase ++ body)) [] [] [] [] [] [] [])) =
      some (cfg (some (initialTarget phase answer).1) (initialTarget phase answer).2.1
        (work body [] [] [] [] [] (initialTarget phase answer).2.2 [])) := by
  change some (TM2.stepAux (code .start) _ _) = _
  cases phase <;> cases answer <;>
    simp [code, go, choose, TM2.stepAux, cfg, ambient, phaseBits,
      initialTarget, work]
  all_goals rfl

theorem replaceTrace (phase : Ambient) (fixed : List (Option Nat)) (i value : Nat)
    (compare reversed : List Bool) :
    (advance machine.step)^[(fixedBits fixed).length + (i + 1) + (natBits value).length]
      (some (cfg (some (.replace (.entry true))) phase
        (work (fixedBits fixed) (encodeWord i) compare [] [] (natBits value) reversed []))) =
      some (cfg (some .reverse) phase (work [] [] compare [] [] []
        ((fixedBits (fixed.set i (some value))).reverse ++ reversed) [])) := by
  have trace := SearchFixedReplaceMachine.replaceTrace replacePlace replacePlace_injective
    Label.replace (some .reverse) code (fun _ => rfl)
    (work [] [] compare [] [] [] [] []) phase fixed i value [] [] [] reversed
  simpa only [machine_step, SearchFixedReplaceMachine.configuration, replaceTapes_eq,
    List.append_nil, cfg] using! trace

theorem zeroControlsStep (phase : Ambient) (input reversed : List Bool) :
    machine.step (cfg (some .zeroControls) phase (work input [] [] [] [] [] reversed [])) =
      some (cfg (some .copyRest) phase (work input [] [] [] [] [] (false :: false :: reversed) [])) := by
  change some (TM2.stepAux (code .zeroControls) _ _) = _
  simp [code, go, TM2.stepAux, cfg, put_work, work]
  all_goals rfl

theorem findTrace (s : State) :
    (advance machine.step)^[findSteps s]
      (some (cfg (some .findBins) (ambient .fill)
        (work (bodyBits s) [] [] [] [] [] [] []))) =
      some (cfg none (ambient .fill)
        (work [] [] [] [] [] [] [] (phaseBits .fill ++ findBody s))) := by
  let tail := rawInstanceBits s.items ++ fixedBits s.fixed
  let header := (encodeWord s.bins).reverse
  have first := unaryCopyTrace .findBins .skipItem rfl s.bins (ambient .fill)
    (work [] [] [] [] [] [] [] []) (encodeWord s.item ++ encodeWord s.label ++ tail) []
  have second := unarySkipTrace .skipItem .skipLabel rfl s.item (ambient .fill)
    (work [] [] [] [] [] [] [] []) (encodeWord s.label ++ tail) header
  have third := unarySkipTrace .skipLabel .zeroControls rfl s.label (ambient .fill)
    (work [] [] [] [] [] [] [] []) tail header
  have fourth := zeroControlsStep (ambient .fill) tail header
  have fifth := copyRestTrace (ambient .fill) tail [] [] [] [] [] (false :: false :: header)
  simp only [io_work, List.append_nil, List.append_assoc] at first second third
  have full := joinTrace (joinTrace (joinTrace (joinTrace first second) third)
    (oneStepTrace fourth)) fifth
  simpa [findSteps, bodyBits, findBody, tail, header, List.reverse_cons,
    List.reverse_reverse, List.append_assoc, Nat.add_assoc] using full

theorem findBudget_le (s : State) :
    1 + findSteps s ≤ rawTime.eval ((stateBits s).length + 1) := by
  have lengths := stateBits_length s
  simp only [findSteps, List.length_append, List.length_cons, List.length_reverse,
    encodeWord_length, rawTime, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  nlinarith

def copyRun (s : State) (answer : Bool) (phase : Ambient) (acc : List Bool)
    (small : acc.length ≤ 1)
    (start : machine.step (cfg (some .start) (ambient .find)
        (work (answer :: stateBits s) [] [] [] [] [] [] [])) =
      some (cfg (some .copyRest) phase (work (bodyBits s) [] [] [] [] [] acc [])))
    (correct : phaseWord phase ++ acc.reverse ++ bodyBits s = stateBits (update s answer)) :
    MachineCanonicalOutput.TerminalRun program (answer :: stateBits s)
      (stateBits (update s answer)) (rawTime.eval (answer :: stateBits s).length) where
  state := (phase, none)
  tapes := work [] [] [] [] [] [] [] (phaseWord phase ++ acc.reverse ++ bodyBits s)
  execution := {
    steps := 1 + (2 * (bodyBits s).length + acc.length + 3)
    evals_in_steps := by
      rw [init_eq]
      change (advance machine.step)^[1 + (2 * (bodyBits s).length + acc.length + 3)] _ = _
      exact joinTrace (oneStepTrace start)
        (copyRestTrace phase (bodyBits s) [] [] [] [] [] acc)
    steps_le_m := by simpa using copyBudget_le s acc.length small }
  output_eq := correct

end BinPackingGap.SearchUpdateMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchStageMachines
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchInitialEmitMachine

open Turing
open BinPackingGames.Foundations.Complexity
open MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open BinPackingGames.Reduction.MachineSubstitution
open SearchInitializeEncoding

def fuelInTime (valid seen : Bool) (n : Nat) (output fixed : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some (finishLabel valid)) (valid, seen) [] output
        (encodeWord n) (encodeWord (n + 1)) [] fixed [])
      (some (cfg none (valid, seen) [] (encodeWord (fuelValue valid n) ++ output)
        (encodeWord n) (encodeWord (n + 1)) [] fixed []))
      (fuelTime valid n) := by
  cases valid with
  | false =>
      simpa only [finishLabel, fuelValue, fuelTime, Bool.false_eq_true, ↓reduceIte,
        encodeWord, List.replicate_zero, List.nil_append, List.singleton_append] using
        oneStep (zeroFuelStep seen output (encodeWord n) (encodeWord (n + 1)) fixed)
  | true =>
      have run := MachineUnaryMultiply.multiplyInTime mulSlots Label.multiply none code
        (fun _ => rfl) (tapes [] output (encodeWord n) (encodeWord (n + 1)) [] fixed [])
        n (n + 1) rfl rfl rfl rfl (true, seen) none
      change StateTransition.EvalsToInTime (TM2.step code)
        ⟨some (.multiply .copyDrain), clean (true, seen),
          tapes [] output (encodeWord n) (encodeWord (n + 1)) [] fixed []⟩
        (some ⟨none, clean (true, seen),
          tapes [] (encodeWord (n * (n + 1)) ++ output)
            (encodeWord n) (encodeWord (n + 1)) [] fixed []⟩)
        (MachineUnaryMultiply.steps n (n + 1))
      simpa [finishLabel, fuelValue, fuelTime, ↓reduceIte,
        MachineUnaryMultiply.resultTapes, mulTape,
        tapes_output, update_output, cfg, clean] using! run

def emitInTime (valid : Bool) (n : Nat) (input : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (cfg (some .start) (false, false) (valid :: (encodeWord n ++ input)) [] [] [] [] [] [])
      (some ⟨none, clean (initialFlags valid n), finishTapes valid n input⟩)
      (rawSteps valid n input.length) := by
  have first := prepareInTime valid n input
  have second := prependRawInTime (initialFlags valid n) input (selectedFixed valid n)
    (encodeWord n) (encodeWord (n + 1)) (residualFixed valid n)
  have third := oneStep (headerStep valid (observed n false)
    (input ++ selectedFixed valid n) (encodeWord n) (encodeWord (n + 1))
    (residualFixed valid n))
  have fourth := fuelInTime valid (observed n false) n (bodyWord valid n input)
    (residualFixed valid n)
  have all := join (join (join first second) third) fourth
  simpa only [rawSteps, finishTapes, outputWord, bodyWord, initialFlags, cfg] using! all

noncomputable def rawRun (data : Data) :
    MachineCanonicalOutput.TerminalRun program (dataBits data)
      (MachineBoundedIteration.inputBits SearchEncoding.stateBits (emit data))
      (rawTime.eval (dataBits data).length) := by
  rcases data with ⟨items, valid⟩
  have run := emitInTime valid items.length (BinaryEncoding.rawInstanceBits items)
  refine {
    state := clean (initialFlags valid items.length)
    tapes := finishTapes valid items.length (BinaryEncoding.rawInstanceBits items)
    execution := ?_
    output_eq := ?_ }
  · simpa only [init_eq, dataBits] using enlarge run (rawSteps_le items valid)
  · change outputWord valid items.length (BinaryEncoding.rawInstanceBits items) = _
    exact outputWord_eq items valid

noncomputable def computation :
    TM2ComputableInPolyTime dataBits
      (MachineBoundedIteration.inputBits SearchEncoding.stateBits) emit :=
  MachineCanonicalOutput.computableInPolyTime program cleanupTapes cleanup_complete
    dataBits (MachineBoundedIteration.inputBits SearchEncoding.stateBits) emit rawTime rawRun

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet program cleanupTapes
    cleanup_complete dataBits (MachineBoundedIteration.inputBits SearchEncoding.stateBits)
    emit rawTime rawRun

end BinPackingGap.SearchInitialEmitMachine

namespace BinPackingGap.SearchInitializeMachine

open Turing BinPackingGames.Foundations.Complexity
open SearchInitializeEncoding

noncomputable def composed :
    TM2ComputableInPolyTime (id : List Bool → List Bool)
      (MachineBoundedIteration.inputBits SearchEncoding.stateBits)
      (fun input => emit (classify input)) :=
  MachineSequential.composeBits (f := id) (g := fun input => emit (classify input))
    shapeComputation
    (MachineSequential.composeBits (f := classify) (g := emit)
      SearchInitialItemsMachine.computation
      SearchInitialEmitMachine.computation)

noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool)
      (MachineBoundedIteration.inputBits SearchEncoding.stateBits)
      SearchMachineComposition.initialize_ where
  tm := composed.tm
  inputAlphabet := composed.inputAlphabet
  outputAlphabet := composed.outputAlphabet
  time := composed.time
  outputsFun input := by
    simpa only [emit_classify] using composed.outputsFun input

theorem finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm := by
  change MachineFiniteAlphabet.FiniteAlphabet composed.tm
  unfold composed
  exact MachineFiniteAlphabet.composeBits (f := id)
    (g := fun input => emit (classify input)) shapeComputation _ shapeFinite
    (MachineFiniteAlphabet.composeBits (f := classify) (g := emit)
      SearchInitialItemsMachine.computation
      SearchInitialEmitMachine.computation SearchInitialItemsMachine.finiteAlphabet
      SearchInitialEmitMachine.finiteAlphabet)

end BinPackingGap.SearchInitializeMachine

end OAI
end


