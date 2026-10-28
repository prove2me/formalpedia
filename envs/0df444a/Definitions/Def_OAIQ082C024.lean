-- Prove2me | Definitions.Def_OAIQ082C024
-- name    : OAIQ082C024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T13:54:58.344991+00:00
-- url     : https://prove2.me/theorems/d04f8d05-ec0a-4bd1-b22a-3729a52baa7b
-- title:
--   Definitions bundle OAIQ082C024 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 200 declarations of OpenAI's Lean: 88 definitions, 3 inductive types or structures, 6 instances and 103 theorems. The definitions and types are `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.Valid`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.carryTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.finishEmitter`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.rootProgram`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan.plan`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.clocksInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.programInTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation.timePolynomial`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.Agrees`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.Ready`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.cellsLabels`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.statement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.steps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly.timePolynomial`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssemblyBounds.cellsPolynomial`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssemblyBounds.timePolynomial`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.FullPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.Alphabet`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.empty`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.forestPorts`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena.initialTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap.inTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.affineRoot`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Emitter.root`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.Selector.positionTest`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.affineProgram`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.compile`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.compileCell`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.compileGlobal`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TermMachine.lookupProgram`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.countdownStatement`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.emitEntry`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.emitLabel`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.emitSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.entry`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.lowerLabel`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.lowerSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration.machine` and 51 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `BinPacking_Arithmetic_NatExpressionBounds`, `BinPacking_Arithmetic_NatExpressionBranch`, `BinPacking_Computation_GraphIterationBounds`, `BinPacking_Computation_MachineHorner`, `BinPacking_Computation_MachineRegularTable`, `BinPacking_Computation_TableIterationFiniteAlphabet`, `BinPacking_CookLevin_Completeness`, `BinPacking_CookLevin_PaddingCellsMachine`, `BinPacking_CookLevin_ProducerFrontStage`, `BinPacking_CookLevin_TermMachine`, `BinPacking_CookLevin_TransitionArena`, `BinPacking_CookLevin_TransitionIteration`, `BinPacking_CookLevin_TransitionIterationTime`, `BinPacking_CookLevin_ValidityComposition`, `BinPacking_CookLevin_ValidityMachine`, `BinPacking_CookLevin_VerifierFront`, `BinPacking_Information_SourceNonempty`, `BinPacking_Machines_GraphPackingGlobalExecution`, `BinPacking_Machines_GraphPackingJobList`, `BinPacking_Machines_PackingJobLoop`, `BinPacking_PCP_Initialization`, `BinPacking_PCP_MachineRawInitialTable`, `BinPacking_PCP_PCPSourceHardness`, `BinPacking_PCP_PreprocessingGuarantees`, `BinPacking_PCP_RawInitialMachineLoop`, `BinPacking_PCP_RawInitialMachineLoopData`, `BinPacking_PCP_RoundTableGap`, `BinPacking_Packing_PackingAssignments`, `BinPacking_Packing_PairExpressionCompiler`, `BinPacking_Search_SearchUpdateMachine`.
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C016`, `OAIQ082C017`, `OAIQ082C018`, `OAIQ082C019`, `OAIQ082C020` and `OAIQ082C021` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ082C027` and `OAIQ082C028`; the proofs of `OAI_BinPackingGames_Foundations_PCP_RoundTableGap_powered_count_gap` and `OAI.BinPackingGames.Foundations.PCP.RoundTableGap.powered_count_gap_oaiq082`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C016
import Definitions.Def_OAIQ082C017
import Definitions.Def_OAIQ082C018
import Definitions.Def_OAIQ082C019
import Definitions.Def_OAIQ082C020
import Definitions.Def_OAIQ082C021

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

variable {α Reg L R N : Type}

variable [DecidableEq Reg]

theorem branchCorrect (op : BinaryOp) (inputs : α → Reg)
    (loc : (Unit ⊕ (L ⊕ R)) ↪ Reg)
    (inputDisjoint : ∀ a node, inputs a ≠ loc node)
    (leftRoot : L) (rightRoot : R)
    (leftValue rightValue : (α → Nat) → Nat)
    (leftCommands rightCommands : List (Command Reg))
    (hLeft : Correct inputs (leftReg loc) leftRoot leftValue leftCommands)
    (hRight : Correct inputs (rightReg loc) rightRoot rightValue rightCommands) :
    Correct inputs loc (.inl ())
      (fun values => applyOp op (leftValue values) (rightValue values))
      ((leftCommands ++ rightCommands) ++
        [command op (branchOperands loc leftRoot rightRoot)]) := by
  intro regs zeroNodes
  have zeroLeft : ∀ node, regs (leftReg loc node) = 0 :=
    fun node => zeroNodes (.inr (.inl node))
  rcases hLeft regs zeroLeft with ⟨readyLeft, outputLeft, frameLeft⟩
  let middle := resultOf leftCommands regs
  have zeroRight : ∀ node, middle (rightReg loc node) = 0 := by
    intro node
    calc
      middle (rightReg loc node) = regs (rightReg loc node) :=
        frameLeft _ (fun left => Ne.symm (leftReg_ne_rightReg loc left node))
      _ = 0 := zeroNodes (.inr (.inr node))
  have inputsUnchanged : (fun a => middle (inputs a)) = (fun a => regs (inputs a)) := by
    funext a
    exact frameLeft _ (fun node => inputDisjoint a (.inr (.inl node)))
  rcases hRight middle zeroRight with ⟨readyRight, outputRight, frameRight⟩
  rw [inputsUnchanged] at outputRight
  have rootAfterLeft : middle (loc (.inl ())) = 0 := by
    calc
      middle (loc (.inl ())) = regs (loc (.inl ())) :=
        frameLeft _ (root_ne_leftReg loc)
      _ = 0 := zeroNodes (.inl ())
  have rootAfterRight : resultOf rightCommands middle (loc (.inl ())) = 0 := by
    calc
      resultOf rightCommands middle (loc (.inl ())) = middle (loc (.inl ())) :=
        frameRight _ (root_ne_rightReg loc)
      _ = 0 := rootAfterLeft
  have leftAfterRight : resultOf rightCommands middle (leftReg loc leftRoot) =
      leftValue (fun a => regs (inputs a)) := by
    calc
      resultOf rightCommands middle (leftReg loc leftRoot) =
          middle (leftReg loc leftRoot) :=
        frameRight _ (leftReg_ne_rightReg loc leftRoot)
      _ = leftValue (fun a => regs (inputs a)) := outputLeft
  have readyLast : Ready [command op (branchOperands loc leftRoot rightRoot)]
      (resultOf rightCommands middle) := by
    refine ⟨?_, trivial⟩
    simpa only [commandReady_command, branchOperands_destination] using rootAfterRight
  have finalResult : resultOf ((leftCommands ++ rightCommands) ++
      [command op (branchOperands loc leftRoot rightRoot)]) regs =
      result (command op (branchOperands loc leftRoot rightRoot))
        (resultOf rightCommands middle) := by
    simp only [resultOf_append, resultOf_cons, resultOf_nil, middle]
  refine ⟨?_, ?_, ?_⟩
  · apply (Ready_append (leftCommands ++ rightCommands)
      [command op (branchOperands loc leftRoot rightRoot)] regs).2
    refine ⟨(Ready_append leftCommands rightCommands regs).2 ⟨readyLeft, readyRight⟩, ?_⟩
    simpa only [resultOf_append] using readyLast
  · rw [finalResult]
    change result (command op (branchOperands loc leftRoot rightRoot))
      (resultOf rightCommands middle) (branchOperands loc leftRoot rightRoot).destination = _
    rw [result_command_destination]
    change applyOp op (resultOf rightCommands middle (leftReg loc leftRoot))
      (resultOf rightCommands middle (rightReg loc rightRoot)) = _
    rw [leftAfterRight, outputRight]
  · intro r outside
    rw [finalResult]
    calc
      result (command op (branchOperands loc leftRoot rightRoot))
          (resultOf rightCommands middle) r = resultOf rightCommands middle r :=
        result_other _ _ r (by
          simpa only [destination_command, branchOperands_destination] using outside (.inl ()))
      _ = middle r := frameRight _ (fun node => outside (.inr (.inr node)))
      _ = regs r := frameLeft _ (fun node => outside (.inr (.inl node)))

end BinPackingGap.NatExpressionCompiler

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Arithmetic_NatExpressionBounds
attribute [-instance] _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.NatExpressionCompiler

open BinaryRegisterProgram

variable {α Reg : Type} [DecidableEq Reg]

theorem compileInto_correct (inputs : α → Reg) (expression : Expr α)
    (nodes : Node expression ↪ Reg) (apart : ∀ a node, inputs a ≠ nodes node) :
    Correct inputs nodes (root expression) (fun values => eval values expression)
      (compileInto inputs expression nodes apart) := by
  induction expression with
  | constant n =>
      intro values empty
      refine ⟨?_, ?_, ?_⟩
      · change values (nodes ()) = 0 ∧ True
        exact ⟨empty (), trivial⟩
      · simp [compileInto, result, destination, value]
      · intro r outside
        simpa only [compileInto, resultOf_cons, resultOf_nil] using
          result_other (.constant (nodes ()) n) values r (outside ())
  | input a =>
      intro values empty
      refine ⟨?_, ?_, ?_⟩
      · change values (nodes ()) = 0 ∧ True
        exact ⟨empty (), trivial⟩
      · simp [compileInto, result, destination, value]
      · intro r outside
        simpa only [compileInto, resultOf_cons, resultOf_nil] using
          result_other (.copy (nodes ()) (inputs a) (apart a ()).symm) values r (outside ())
  | add left right ihLeft ihRight =>
      exact branchCorrect .add inputs nodes apart (root left) (root right)
        (fun values => eval values left) (fun values => eval values right)
        (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
        (ihLeft (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (ihRight (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
  | mul left right ihLeft ihRight =>
      exact branchCorrect .mul inputs nodes apart (root left) (root right)
        (fun values => eval values left) (fun values => eval values right)
        (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
        (ihLeft (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (ihRight (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
  | monus left right ihLeft ihRight =>
      exact branchCorrect .monus inputs nodes apart (root left) (root right)
        (fun values => eval values left) (fun values => eval values right)
        (compileInto inputs left (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (compileInto inputs right (rightReg nodes) (fun a node => apart a (.inr (.inr node))))
        (ihLeft (leftReg nodes) (fun a node => apart a (.inr (.inl node))))
        (ihRight (rightReg nodes) (fun a node => apart a (.inr (.inr node))))

end BinPackingGap.NatExpressionCompiler

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PreprocessingGuarantees
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

theorem regularVertices_le (t : GraphTables.Table) :
    regularVertices t ≤ ExpanderFamily.growth * t.darts := vertexCount_le t

theorem vertices_le_of_positive (t : GraphTables.Table) (ht : 0 < t.darts) :
    vertices t ≤ ExpanderFamily.growth ^ 2 * t.darts := by
  have hr : 0 < regularVertices t := ht.trans_le (regularVertices_ge_darts t)
  calc
    _ ≤ ExpanderFamily.growth * regularVertices t :=
      (PreprocessingLevels.paddedSize_bounds hr).2
    _ ≤ ExpanderFamily.growth * (ExpanderFamily.growth * t.darts) :=
      Nat.mul_le_mul_left _ (regularVertices_le t)
    _ = _ := by ring

end BinPackingGames.Foundations.PCP.PreprocessingTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def multiplyInTime (slots : Fin 5 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (p : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ label, p (labels label) = statement slots labels exit label)
    (base : K → List Bool) (a b : ℕ)
    (operandA : base (slots 0) = encodeWord a)
    (operandB : base (slots 1) = encodeWord b)
    (counterEmpty : base (slots 3) = []) (scratchEmpty : base (slots 4) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step p)
      ⟨some (labels .copyDrain), ((ambient, ()), register), base⟩
      (some ⟨exit, ((ambient, ()), none), resultTapes slots base (a * b)⟩) (steps a b) where
  steps := steps a b
  evals_in_steps := multiplyTrace slots labels exit p atLabels base a b operandA operandB
    counterEmpty scratchEmpty ambient register
  steps_le_m := Nat.le_refl _

end BinPackingGames.Foundations.Complexity.MachineUnaryMultiply

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Information_SourceNonempty
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Hastad.SourceHeaderCounts

open Turing Complexity
open MachineComposition

namespace Eval

open CookLevin.PolynomialMachine

variable {K Λ σ : Type} [DecidableEq K]

theorem trace (p : Polynomial Nat) (slots : MachineHorner.Layout (width p) ↪ K)
    (labels : Label p → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement p slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl 0)) = encodeWord n)
    (hcoeff : ∀ i : Fin (width p), base (slots (.inr i)) = [])
    (clean : MachineHorner.Clean slots base) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps p n]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
  have hp : (advance (TM2.step program))^[1]
      (some ⟨some (labels (start p)), ((ambient, ()), register), base⟩) =
      some ⟨some (labels (inner p .start)), ((ambient, ()), register), prepared p slots base⟩ := by
    change some (TM2.stepAux (program (labels (start p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (prependFields _ _ _) _ _) = _
    rw [stepAux_prependFields]
    rfl
  have hh := MachineHorner.hornerTrace slots (fun l => labels (inner p l))
    (some (labels (finish p))) program (fun l => atLabels (inner p l))
    (prepared p slots base) n (digit p) (by simpa using hinput)
    (fun i => prepared_digit p slots base i (hcoeff i))
    (by
      constructor
      · simpa using clean.accA
      · simpa using clean.accB
      · simpa using clean.counter
      · simpa using clean.scratch) ambient register
  rw [hornerValue_eq_eval] at hh
  have hc : (advance (TM2.step program))^[1]
      (some ⟨some (labels (finish p)), ((ambient, ()), none),
        MachineHorner.resultTapes slots (prepared p slots base) (p.eval n)⟩) =
      some ⟨exit, ((ambient, ()), none), MachineHorner.resultTapes slots base (p.eval n)⟩ := by
    change some (TM2.stepAux (program (labels (finish p))) _ _) = _
    rw [atLabels]
    change some (TM2.stepAux (clearFields _ _ _) _ _) = _
    rw [stepAux_clearFields, clear_result p slots base _ hcoeff]
    cases exit <;> rfl
  rw [show steps p n = 1 + (MachineHorner.steps n (digit p) (width p) + 1) by
    unfold steps; omega, Function.iterate_add_apply, Function.iterate_add_apply, hp, hh, hc]

end Eval

end BinPackingGames.Foundations.Hastad.SourceHeaderCounts

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RoundTableGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RoundTables

theorem build_size_le (H : BaseTable) (table : GraphTables.Table)
    (ht : 0 < table.darts) :
    (build H table).vertices + (build H table).darts ≤
      sizeFactor * (table.vertices + table.darts) := by
  have hv := PreprocessingTables.vertices_le_of_positive table ht
  have he : (powered H table).vertices + (powered H table).darts =
      PreprocessingTables.vertices table *
        (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) := by
    rw [powered_vertices, powered_darts]
    ring
  have hp := Nat.mul_le_mul_right
    (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1)) hv
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((powered H table).vertices + (powered H table).darts) :=
      AlphabetTableBounds.build_total_le (powered H table)
    _ = AlphabetGraphBounds.sizeFactor alphabet *
        (PreprocessingTables.vertices table *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) := by rw [he]
    _ ≤ AlphabetGraphBounds.sizeFactor alphabet *
        ((ExpanderFamily.growth ^ 2 * table.darts) *
          (1 + 2 * PreprocessingTables.degree ^ (walkParameter + 1))) :=
      Nat.mul_le_mul_left _ hp
    _ = sizeFactor * table.darts := by unfold sizeFactor; ring
    _ ≤ sizeFactor * (table.vertices + table.darts) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

theorem step_size (H : BaseTable) (input : Input) :
    size (step H input) ≤ sizeFactor * size input := build_size_le H input.val input.property

end BinPackingGames.Foundations.PCP.RoundTables

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_GraphIterationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

theorem intermediate_size (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    size (TableIteration.run H i input) ≤ PCPIterationMachine.sizeEnvelope sizeFactor (size input) := by
  apply PCPIterationMachine.semanticSize_bound
    (fun j => size (TableIteration.run H j input)) sizeFactor (size input)
    sizeFactor_positive (Nat.le_succ _) _ i hi
  intro j _
  exact step_size H (TableIteration.run H j input)

theorem intermediate_bits (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    (words H input i).length ≤ lengthPolynomial.eval (countedBits input).length := by
  have hsize := intermediate_size H input i hi
  have hinput := (size_le_inputBits input).trans (inputBits_le_countedBits input)
  have heval := MachineComposition.natPolynomial_eval_mono
    (PCPIterationMachine.sizePolynomial sizeFactor) hinput
  rw [PCPIterationMachine.sizePolynomial_eval, PCPIterationMachine.sizePolynomial_eval] at heval
  have hs := hsize.trans heval
  have htable : (TableIteration.runTables H i input.val).vertices +
      (TableIteration.runTables H i input.val).darts ≤
        PCPIterationMachine.sizeEnvelope sizeFactor (countedBits input).length := by
    rw [← TableIteration.run_val]
    exact hs
  rw [lengthPolynomial, Polynomial.eval_comp, PCPIterationMachine.sizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ htable

end BinPackingGames.Foundations.Complexity.GraphIterationBounds

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_MachineRegularTable
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open BinPackingGames.Foundations.PCP

namespace Top

instance tapeLawfulBEq : LawfulBEq Tape where
  eq_of_beq := of_decide_eq_true
  rfl := of_decide_eq_self_eq_true _

end Top

end BinPackingGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineLoopData
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.LiteralSlotGraph.instDecidableConflict _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

theorem formulaStartTrace (F : Target.Formula) :
    (MachineComposition.advance (TM2.step program))^[
        3 * F.variables + 5 * F.clauses.length + 13]
      (some (initList machine (formulaBits F))) =
      some ⟨some .guard, initialState,
        startTapes F.variables F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩ := by
  simpa only [formulaBits, formulaWords, encodeWords_append] using
    startTrace F.variables F.clauses.length (encodeWords (F.clauses.flatMap clauseWords))

end BinPackingGames.Foundations.PCP.RawInitialMachineStart

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_RawInitialMachineLoop
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.RawInitialMachineLoop

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

theorem loopTrace {n : Nat} (i : Nat) (cs : List (Clause n))
    (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[loopTime i cs]
      (some ⟨some .guard, state, loopTapes n i cs.length (clauseInput cs) rev⟩) =
      some ⟨some (.scan .dummyVariables), (finalSigns state.1 cs, none),
        finishTapes n (i + cs.length) ((encodeWords (clauseOutput n i cs)).reverse ++ rev)⟩ := by
  induction cs generalizing i rev state with
  | nil =>
      have h := RawInitialMachineBody.guardTrace_zero n i [] rev state
      rw [empty_loopTapes] at h
      simpa only [loopTime, List.length_nil, clauseInput_nil, clauseOutput_nil,
        finalSigns, encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero,
        empty_loopTapes] using h
  | cons c cs ih =>
      have first := bodyTrace i cs.length c (clauseInput cs) rev state
      have rest := ih (i + 1)
        ((encodeWords (RawInitialRows.clauseWords n i
          (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ rev)
        (RawInitialRows.clauseSigns c, none)
      have total := trace_trans _ first rest
      have hi : i + 1 + cs.length = i + (cs.length + 1) := by omega
      simpa only [loopTime, List.length_cons, clauseInput_cons, clauseOutput_cons,
        encodeWords_append, List.reverse_append, List.append_assoc, finalSigns, hi] using total

end BinPackingGames.Foundations.PCP.RawInitialMachineLoop

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_MachineRawInitialTable
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.LiteralSlotGraph.instDecidableConflict _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.MachineRawInitialTable

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineLoop

theorem machineTrace (F : Formula) :
    (MachineComposition.advance (TM2.step program))^[fullBudget F]
      (some (initList machine (formulaBits F))) =
      some (haltList machine (GraphTables.tableBits (RawInitialTables.table F))) := by
  have startup := RawInitialMachineStart.formulaStartTrace F
  rw [startTapes_eq] at startup
  have loop := loopTrace 0 F.clauses
    (encodeWords [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse
    initialState
  have hprefix : (encodeWords (clauseOutput F.variables 0 F.clauses)).reverse ++
      (encodeWords [F.variables + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse =
      (prefixBits F).reverse := by
    simp only [prefixBits, encodeWords_append, List.reverse_append]
  rw [hprefix, Nat.zero_add] at loop
  have finish := RawInitialMachineFinish.finishTrace F.variables F.clauses.length
    (prefixBits F).reverse (finalSigns initialState.1 F.clauses, none)
  rw [List.reverse_reverse, ← outputBits F] at finish
  have total := trace_trans _ (trace_trans _ startup loop) finish
  have time : (3 * F.variables + 5 * F.clauses.length + 13 + loopTime 0 F.clauses) +
      (3 * F.variables + 5 * F.clauses.length + 17 +
        (encodeWords (RawInitialRows.dummyWords F.variables F.clauses.length)).length +
        (prefixBits F).reverse.length) = fullBudget F := by
    rw [fullBudget, outputBits, List.length_append, List.length_reverse]
    omega
  simpa only [time] using total

def outputsInTime (F : Formula) :
    TM2OutputsInTime machine (formulaBits F)
      (some (GraphTables.tableBits (RawInitialTables.table F)))
      (timePolynomial.eval (formulaBits F).length) where
  steps := fullBudget F
  evals_in_steps := machineTrace F
  steps_le_m := fullBudget_le F

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaEncoding.encode GraphTables.encoding.encode
      RawInitialTables.table where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun F := by
    change TM2OutputsInTime machine ((formulaBits F).map id)
      (some ((GraphTables.tableBits (RawInitialTables.table F)).map id))
      (timePolynomial.eval (formulaBits F).length)
    have hi := @List.map_id (machine.Γ machine.k₀) (formulaBits F)
    have ho := @List.map_id (machine.Γ machine.k₁)
      (GraphTables.tableBits (RawInitialTables.table F))
    rw [hi, ho]
    exact outputsInTime F

end BinPackingGames.Foundations.PCP.MachineRawInitialTable

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_TableIterationFiniteAlphabet
attribute [-instance] _root_.OAI.BinPackingGap.LiteralSlotGraph.instDecidableConflict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.MachineTableIteration

open Turing PCP RoundTables GraphIterationBounds

variable (H : BaseTable)
  (body : TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits (build H))

noncomputable def countedCertificate :
    TM2ComputableInPolyTime countedBits GraphTables.tableBits (finalTable H) where
  tm := MachineRepeat.machine body.tm body.inputAlphabet body.outputAlphabet
  inputAlphabet := body.inputAlphabet
  outputAlphabet := body.inputAlphabet
  time := runtimePolynomial body.time
  outputsFun input := by
    let budgets := fun i => body.time.eval (words H input i).length
    have runs (i : Nat) (_hi : i < count input) :
        TM2OutputsInTime body.tm ((words H input i).map body.inputAlphabet.symm)
          (some ((words H input (i + 1)).map body.outputAlphabet.symm)) (budgets i) := by
      exact body.outputsFun (TableIteration.runTables H i input.val)
    let run := MachineRepeat.executeSequence body.tm body.inputAlphabet body.outputAlphabet
      (count input) (words H input) budgets runs
    have start : encodeWord (count input) ++ words H input 0 = countedBits input := rfl
    have finish : words H input (count input) = GraphTables.tableBits (finalTable H input) := rfl
    rw [start, finish] at run
    refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
    let N := (countedBits input).length
    let L := lengthPolynomial.eval N
    let B := body.time.eval L
    have hl (i : Nat) (hi : i ≤ count input) : (words H input i).length ≤ L :=
      intermediate_bits H input i hi
    have hb (i : Nat) (hi : i < count input) : budgets i ≤ B :=
      MachineComposition.natPolynomial_eval_mono body.time (hl i hi.le)
    have hloop := MachineRepeat.loopBudget_le (count input) (words H input) budgets B L hb hl
    have hc : count input ≤ N + 1 := count_le input
    rw [runtimePolynomial_eval]
    calc
      run.steps ≤ count input + 1 + MachineRepeat.loopBudget (count input) (words H input) budgets :=
        run.steps_le_m
      _ ≤ count input + 1 + (count input * (B + 2 * L + 3) + 2 * L + 3) :=
        Nat.add_le_add_left hloop _
      _ = count input * (B + 2 * L + 4) + 2 * L + 4 := by ring
      _ ≤ (N + 1) * (B + 2 * L + 4) + 2 * L + 4 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) _) _

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime inputBits GraphTables.tableBits (finalTable H) :=
  MachineSequential.composeBits counterCertificate (countedCertificate H body)

noncomputable def initialCertificate :
    TM2ComputableInPolyTime formulaBits inputBits initial where
  toTM2ComputableAux := MachineRawInitialTable.computableInPolyTime.toTM2ComputableAux
  time := MachineRawInitialTable.computableInPolyTime.time
  outputsFun F := MachineRawInitialTable.computableInPolyTime.outputsFun F

noncomputable def tableCertificate :
    TM2ComputableInPolyTime formulaBits GraphTables.tableBits (TableIteration.outputTable H) := by
  change TM2ComputableInPolyTime formulaBits GraphTables.tableBits
    (fun F => finalTable H (initial F))
  exact MachineSequential.composeBits (f := initial) (g := finalTable H)
    initialCertificate (computableInPolyTime H body)

noncomputable def gapMapCertificate :
    TM2ComputableInPolyTime formulaBits formulaBits (TableIteration.gapMap H) :=
  MachineSequential.composeBits (f := TableIteration.outputTable H) (g := FinalTableFormula.output)
    (tableCertificate H body)
    FinalCNFMachine.Program.computableInPolyTime

end BinPackingGames.Foundations.Complexity.MachineTableIteration

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted emitted_append emitted_other emitted_nil)

variable {K Λ σ : Type} [DecidableEq K]

namespace SelectorLoop

theorem trace (slots : Fin 5 ↪ K) (labels : Label → Λ) (done : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels done l)
    (base : K → List Bool) (count start : Nat)
    (scratchEmpty : base (slots 2) = []) (ambient : σ) :
    (advance (TM2.step program))^[steps count start]
      (some ⟨some (labels .guard), clean ambient, frame slots base count start⟩) =
      some ⟨some done, clean ambient,
        frame slots (emitted (slots 3) (slots 4) base (tokens count start)) 0 (start + count)⟩ := by
  induction count generalizing base start with
  | zero =>
    have h := MachineUnaryCounter.guardTrace_zero (slots 0) (labels .guard)
      (labels (.input .tag)) done program (atLabels .guard)
      (frame slots base 0 start) [] (ambient, false) none
    simpa only [counter_frame, steps, tokens_zero, emitted_nil, Nat.add_zero, clean] using h
  | succ count ih =>
    have hg := MachineUnaryCounter.guardTrace_succ (slots 0) (labels .guard)
      (labels (.input .tag)) done program (atLabels .guard)
      (frame slots base count start) count [] (ambient, false) none
    simp only [counter_frame] at hg
    have hs : frame slots base count start (slots 2) = [] := by
      simpa [frame, slots.injective.eq_iff] using scratchEmpty
    have hp := ClashMachine.Input.trace (inputMap.trans slots) (fun l => labels (.input l))
      (some (labels .increment)) program (fun _ => atLabels _)
      (frame slots base count start) start (frame_current slots base count start) hs ambient
    change (advance (TM2.step program))^[ClashMachine.Input.steps start]
      (some ⟨some (labels (.input .tag)), clean ambient, frame slots base count start⟩) =
      some ⟨some (labels .increment), clean ambient,
        emitted (slots 3) (slots 4) (frame slots base count start) [.input start]⟩ at hp
    rw [emitted_frame] at hp
    let nextBase := emitted (slots 3) (slots 4) base [.input start]
    have hn : (advance (TM2.step program))^[1]
        (some ⟨some (labels .increment), clean ambient, frame slots nextBase count start⟩) =
        some ⟨some (labels .guard), clean ambient, frame slots nextBase count (start + 1)⟩ := by
      change some (TM2.stepAux (program (labels .increment)) _ _) = _
      rw [atLabels, statement]
      simp only [TM2.stepAux, frame_current, increment_frame]
    have hns : nextBase (slots 2) = [] := by
      simpa [nextBase, emitted, slots.injective.eq_iff] using scratchEmpty
    have hr := ih nextBase (start + 1) hns
    have h := chain (chain (chain hg hp) hn) hr
    rw [show start + 1 + count = start + (count + 1) by omega] at h
    simp only [nextBase, emitted_append (slots 3) (slots 4)
      (slots.injective.ne (by decide : (3 : Fin 5) ≠ 4)), ← tokens_succ] at h
    exact h

end SelectorLoop

namespace Nonempty

theorem trace (slots : Fin 7 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[steps q]
      (some ⟨some (labels .initialize_), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 5) (slots 6) base (nonemptyTokens q)⟩ := by
  let started := Function.update base (slots 2) (encodeWord 0)
  let remaining := Function.update started (slots 1) (encodeWord (q + 1))
  let prepared := Function.update remaining (slots 4) (encodeWord (q + 1))
  have hi : (advance (TM2.step program))^[1]
      (some ⟨some (labels .initialize_), clean ambient, base⟩) =
      some ⟨some (labels (.remaining .seed)), clean ambient, started⟩ := by
    change some (TM2.stepAux (program (labels .initialize_)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, started, ready.currentEmpty, encodeWord]
  have hsq : started (slots 0) = encodeWord q := by
    simpa [started, slots.injective.eq_iff] using ready.boundWord
  have hss : started (slots 3) = [] := by
    simpa [started, slots.injective.eq_iff] using ready.scratchEmpty
  have hr := MachineUnaryAffineAt.seededAffineTrace (slots 0) (slots 3) (slots 1)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) 1 1
    (labels (.remaining .seed)) (labels (.remaining .scan)) (labels (.remaining .restore))
    (some (labels (.closure .seed))) program
    (atLabels (.remaining .seed)) (atLabels (.remaining .scan)) (atLabels (.remaining .restore))
    started q [] (by simpa using hsq) hss (ambient, false) none
  have hrs : started (slots 1) = [] := by
    simpa [started, slots.injective.eq_iff] using ready.remainingEmpty
  simp only [Nat.one_mul, hrs, List.append_nil] at hr
  change (advance (TM2.step program))^[2 * (q + 1) + 1]
    (some ⟨some (labels (.remaining .seed)), clean ambient, started⟩) =
    some ⟨some (labels (.closure .seed)), clean ambient, remaining⟩ at hr
  have hrq : remaining (slots 0) = encodeWord q := by
    simpa [remaining, slots.injective.eq_iff] using hsq
  have hsc : remaining (slots 3) = [] := by
    simpa [remaining, slots.injective.eq_iff] using hss
  have hc := MachineUnaryAffineAt.seededAffineTrace (slots 0) (slots 3) (slots 4)
    (slots.injective.ne (by decide)) (slots.injective.ne (by decide))
    (slots.injective.ne (by decide)) 1 1
    (labels (.closure .seed)) (labels (.closure .scan)) (labels (.closure .restore))
    (some (labels (.selector .guard))) program
    (atLabels (.closure .seed)) (atLabels (.closure .scan)) (atLabels (.closure .restore))
    remaining q [] (by simpa using hrq) hsc (ambient, false) none
  have hrc : remaining (slots 4) = [] := by
    simpa [remaining, started, slots.injective.eq_iff] using ready.closureEmpty
  simp only [Nat.one_mul, hrc, List.append_nil] at hc
  change (advance (TM2.step program))^[2 * (q + 1) + 1]
    (some ⟨some (labels (.closure .seed)), clean ambient, remaining⟩) =
    some ⟨some (labels (.selector .guard)), clean ambient, prepared⟩ at hc
  let loopBase := Function.update base (slots 4) (encodeWord (q + 1))
  have hprepared : prepared = SelectorLoop.frame (loopMap.trans slots) loopBase (q + 1) 0 := by
    funext k
    by_cases h₁ : k = slots 1
    · subst k; simp [prepared, remaining, started, frame_updates, loopBase, slots.injective.eq_iff]
    · by_cases h₂ : k = slots 2
      · subst k; simp [prepared, remaining, started, frame_updates, loopBase, slots.injective.eq_iff]
      · by_cases h₄ : k = slots 4
        · subst k; simp [prepared, remaining, started, frame_updates, loopBase, slots.injective.eq_iff]
        · simp [prepared, remaining, started, frame_updates, loopBase, h₁, h₂, h₄]
  have hls : loopBase ((loopMap.trans slots) 2) = [] := by
    simpa [loopBase, loopMap, slots.injective.eq_iff] using ready.scratchEmpty
  have hl := SelectorLoop.trace (loopMap.trans slots) (fun l => labels (.selector l))
    (labels .orSeed) program (fun _ => atLabels _) loopBase (q + 1) 0 hls ambient
  let afterLoop := SelectorLoop.frame (loopMap.trans slots)
    (emitted (slots 5) (slots 6) loopBase (SelectorLoop.tokens (q + 1) 0)) 0 (q + 1)
  rw [Nat.zero_add] at hl
  change (advance (TM2.step program))^[SelectorLoop.steps (q + 1) 0]
    (some ⟨some (labels (.selector .guard)), clean ambient,
      SelectorLoop.frame (loopMap.trans slots) loopBase (q + 1) 0⟩) =
    some ⟨some (labels .orSeed), clean ambient, afterLoop⟩ at hl
  rw [← hprepared] at hl
  have hac : afterLoop (slots 4) = encodeWord (q + 1) := by
    simp [afterLoop, frame_updates, loopBase, emitted, slots.injective.eq_iff]
  have hstart : OrClosure.frame (closurePorts slots) afterLoop (encodeWord (q + 1) ++ [])
      (afterLoop (slots 5)) (afterLoop (slots 6)) = afterLoop := by
    rw [List.append_nil, ← hac]
    change OrClosure.frame (closurePorts slots) afterLoop
      (afterLoop (closurePorts slots).remaining) (afterLoop (closurePorts slots).reversed)
      (afterLoop (closurePorts slots).count) = afterLoop
    exact OrClosure.frame_self (closurePorts slots) afterLoop
  have ho := OrClosure.closureTrace (closurePorts slots) (labels .orSeed) (labels .orLoop)
    (some (labels .cleanup)) program (atLabels .orSeed) (atLabels .orLoop)
    afterLoop (q + 1) [] (afterLoop (slots 5)) (afterLoop (slots 6)) (ambient, false) none
  rw [hstart, List.append_nil] at ho
  have hclosed := closed_frame (closurePorts slots) afterLoop (q + 1)
  change OrClosure.frame (closurePorts slots) afterLoop (encodeWord 0)
      ((tokenBits (closeOr (q + 1))).reverse ++ afterLoop (slots 5))
      (List.replicate (q + 1 + 1) true ++ afterLoop (slots 6)) =
    emitted (slots 5) (slots 6) (Function.update afterLoop (slots 4) (encodeWord 0))
      (closeOr (q + 1)) at hclosed
  rw [hclosed] at ho
  let closed := emitted (slots 5) (slots 6)
    (Function.update afterLoop (slots 4) (encodeWord 0)) (closeOr (q + 1))
  change (advance (TM2.step program))^[q + 3]
    (some ⟨some (labels .orSeed), clean ambient, afterLoop⟩) =
    some ⟨some (labels .cleanup), clean ambient, closed⟩ at ho
  have hcr : closed (slots 1) = encodeWord 0 := by
    simp [closed, afterLoop, frame_updates, emitted, slots.injective.eq_iff]
  have hcc : closed (slots 4) = encodeWord 0 := by
    simp [closed, emitted, slots.injective.eq_iff]
  let cleared := Function.update (Function.update closed (slots 1) []) (slots 4) []
  have hcleanup : (advance (TM2.step program))^[1]
      (some ⟨some (labels .cleanup), clean ambient, closed⟩) =
      some ⟨some (labels .drain), clean ambient, cleared⟩ := by
    change some (TM2.stepAux (program (labels .cleanup)) _ _) = _
    rw [atLabels, statement]
    simp [TM2.stepAux, hcr, hcc, encodeWord, cleared, slots.injective.eq_iff]
  have hcur : cleared (slots 2) = encodeWord (q + 1) := by
    simp [cleared, closed, afterLoop, frame_updates, emitted, slots.injective.eq_iff]
  have hd := MachineDrain.drainTrace (slots 2) (labels .drain) exit program (atLabels .drain)
    cleared (encodeWord (q + 1)) (ambient, false) none
  rw [← hcur, Function.update_eq_self] at hd
  rw [hcur, encodeWord_length] at hd
  have hfinish : Function.update cleared (slots 2) [] =
      emitted (slots 5) (slots 6) base (nonemptyTokens q) := by
    have hmove (k : Fin 7) (hk₅ : k ≠ 5) (hk₆ : k ≠ 6)
        (b : K → List Bool) (word : List Bool) (ts : List Token) :=
      emitted_update (slots 5) (slots 6) (slots k)
        (slots.injective.ne hk₅) (slots.injective.ne hk₆) b word ts
    simp only [cleared, closed, afterLoop, frame_updates, loopBase,
      hmove 1 (by decide) (by decide), hmove 2 (by decide) (by decide),
      hmove 4 (by decide) (by decide),
      emitted_append (slots 5) (slots 6)
        (slots.injective.ne (by decide : (5 : Fin 7) ≠ 6)), tokens_nonempty]
    funext k
    by_cases h₁ : k = slots 1
    · subst k; simp [emitted, slots.injective.eq_iff, ready.remainingEmpty]
    · by_cases h₂ : k = slots 2
      · subst k; simp [emitted, slots.injective.eq_iff, ready.currentEmpty]
      · by_cases h₄ : k = slots 4
        · subst k; simp [emitted, slots.injective.eq_iff, ready.closureEmpty]
        · simp [h₁, h₂, h₄]
  rw [hfinish] at hd
  exact chain (chain (chain (chain (chain (chain hi hr) hc) hl) ho) hcleanup) hd

end Nonempty

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_PaddingCellsMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

open Turing PostfixModel VerifierCircuit InitializationTemplate
open Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqΛTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqσTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl.instDecidableEqΓTmBoolComputation
theorem trace (V : NPVerifier) (p : Ports K) (entry : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (code : program entry = statement V p exit)
    (base : K → List Bool) (state : σ) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some entry, state, base⟩) =
      some ⟨exit, state, emitted p base (tokens V)⟩ :=
  literalTrace p (tokens V) entry exit program code base state

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationControl

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ValidityComposition
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

open Turing MachineComposition PostfixModel InitializationTemplate
open ClashMachine (State clean emitted)

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (ValidityMachine.Alphabet (K := K)) Λ (State σ)
  | .nonempty l => Nonempty.statement (nonemptyMap.trans slots)
      (fun l => labels (.nonempty l)) (some (labels (.clash .start))) l
  | .clash l => ClashMachine.Full.statement slots (fun l => labels (.clash l))
      (some (labels .finish)) l
  | .finish => ClashMachine.literal (slots 7) (slots 8) [.not, .and]
      (Reduction.MachineTransfer.exitAt (slots 7) exit)

theorem trace (slots : Fin 10 ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (ValidityMachine.Alphabet (K := K)) Λ (State σ))
    (atLabels : ∀ l, program (labels l) = statement slots labels exit l)
    (base : K → List Bool) (q : Nat) (ready : ClashMachine.Full.Ready slots base q) (ambient : σ) :
    (advance (TM2.step program))^[steps q]
      (some ⟨some (labels (.nonempty .initialize_)), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) base (validityTokens q)⟩ := by
  have nr : Nonempty.Ready (nonemptyMap.trans slots) base q := {
    boundWord := ready.source
    remainingEmpty := ready.empty 1 (by decide) (by decide) (by decide)
    currentEmpty := ready.empty 3 (by decide) (by decide) (by decide)
    scratchEmpty := ready.empty 5 (by decide) (by decide) (by decide)
    closureEmpty := ready.empty 9 (by decide) (by decide) (by decide) }
  have hn := Nonempty.trace (nonemptyMap.trans slots) (fun l => labels (.nonempty l))
    (some (labels (.clash .start))) program (fun _ => atLabels _) base q nr ambient
  let afterNonempty := emitted (slots 7) (slots 8) base (nonemptyTokens q)
  change (advance (TM2.step program))^[Nonempty.steps q]
    (some ⟨some (labels (.nonempty .initialize_)), clean ambient, base⟩) =
    some ⟨some (labels (.clash .start)), clean ambient, afterNonempty⟩ at hn
  have hc := ClashMachine.Full.trace slots (fun l => labels (.clash l))
    (some (labels .finish)) program (fun _ => atLabels _)
    afterNonempty q (ready.emitted (nonemptyTokens q)) ambient
  let afterClash := emitted (slots 7) (slots 8) afterNonempty (clashTokens q)
  have hf : (advance (TM2.step program))^[1]
      (some ⟨some (labels .finish), clean ambient, afterClash⟩) =
      some ⟨exit, clean ambient, emitted (slots 7) (slots 8) afterClash [.not, .and]⟩ := by
    change some (TM2.stepAux (program (labels .finish)) _ _) = _
    rw [atLabels, statement, ClashMachine.stepAux_literal (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8))]
    cases exit <;> rfl
  have h := chain (chain hn hc) hf
  simpa only [steps, afterClash, afterNonempty,
    ClashMachine.emitted_append (slots 7) (slots 8)
      (slots.injective.ne (by decide : (7 : Fin 10) ≠ 8)), validityTokens] using h

end BinPackingGames.Foundations.Complexity.CookLevin.ValidityMachine.Full

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TermMachine
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

open Turing MachineComposition TransitionTemplate PostfixModel

attribute [instance] Emitter.finite

theorem lookupTapes_injective : Function.Injective lookupTapes := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [lookupTapes]

def lookupProgram (address : Nat) : LookupLabel → TM2.Stmt Alphabet LookupLabel State
  | .start => Reduction.MachineSubstitution.pushWord .address (encodeWord address).reverse
      (.goto fun _ => .lookup (.run .copyFirst))
  | .lookup label => MachinePreservingLookupClean.statement lookupTapes LookupLabel.lookup
      (some .tag) label
  | .tag => Reduction.MachineSubstitution.pushWord .reversed (encodeWord 5)
      (.goto fun _ => .move)
  | .move => Reduction.MachineTransfer.loopAt .value .reversed id false .move (some .finish)
  | .finish => .pop .address (fun _ _ => initialState)
      (.push .count (fun _ => true) .halt)

theorem lookupTailTrace (seedAddress : Nat) (input : Input) (address : Nat)
    (selected : input.roots[address]? = some (rootLookup input.roots address))
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (lookupProgram seedAddress)))^[
      MachinePreservingLookupClean.steps input.roots address +
        rootLookup input.roots address + 4]
      (some ⟨some (.lookup (.run .copyFirst)), initialState,
        Function.update base .address (encodeWord address)⟩) =
      some ⟨none, initialState,
        emitTapes base [.input (rootLookup input.roots address)]⟩ := by
  let wire := rootLookup input.roots address
  let seeded := Function.update base .address (encodeWord address)
  let found := Function.update (Function.update base .address (encodeWord 0))
    .value (encodeWord wire)
  let tagged := Function.update found .reversed ((encodeWord 5).reverse ++ base .reversed)
  let moved := Function.update (Function.update base .address (encodeWord 0))
    .reversed ((encodeWord wire).reverse ++ (encodeWord 5).reverse ++ base .reversed)
  have haddress := frame.clean .address (by rfl)
  have hvalue := frame.clean .value (by rfl)
  have hcopy := frame.clean .copy (by rfl)
  have hscratch := frame.clean .scratch (by rfl)
  have lookup := MachinePreservingLookupClean.traceAt_fromTapes
    lookupTapes lookupTapes_injective LookupLabel.lookup (some .tag)
    (lookupProgram seedAddress) (fun _ => rfl) seeded input.roots
    (by simpa [seeded, lookupTapes] using frame.rootsWord)
    (by simpa [seeded, lookupTapes] using hscratch)
    address wire selected []
    (by simp [seeded, lookupTapes])
    (by simpa [seeded, lookupTapes] using hcopy) ((), false) none
  have lookupFrame : MachinePreservingLookup.initialTapes lookupTapes seeded 0 [] []
      (encodeWord wire ++ seeded (lookupTapes 3)) = found := by
    funext tape
    cases tape <;> simp [MachinePreservingLookup.initialTapes, MachineLookup.tapes,
      lookupTapes, seeded, found, hvalue, hcopy]
  rw [lookupFrame] at lookup
  have tag : (advance (TM2.step (lookupProgram seedAddress)))^[1]
      (some ⟨some .tag, initialState, found⟩) =
      some ⟨some .move, initialState, tagged⟩ := by
    change some (TM2.stepAux (lookupProgram seedAddress .tag) initialState found) = _
    simp [lookupProgram, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, tagged, found]
  have move := Reduction.MachineTransfer.transferAt_fromTapes
    (Γ := Alphabet) .value .reversed (by decide) id false LookupLabel.move
    (some LookupLabel.finish) (lookupProgram seedAddress) rfl tagged ((), false) none
  have valueWord : tagged .value = encodeWord wire := by simp [tagged, found]
  have moveFrame : Reduction.MachineTransfer.tapesAt .value .reversed tagged []
      ((tagged .value).reverse.map id ++ tagged .reversed) = moved := by
    funext tape
    cases tape <;> simp [Reduction.MachineTransfer.tapesAt, tagged, found, moved,
      hvalue, List.append_assoc]
  rw [moveFrame, valueWord, encodeWord_length] at move
  have finish : (advance (TM2.step (lookupProgram seedAddress)))^[1]
      (some ⟨some .finish, initialState, moved⟩) =
      some ⟨none, initialState, emitTapes base [.input wire]⟩ := by
    change some (TM2.stepAux (lookupProgram seedAddress .finish) initialState moved) = _
    simp only [lookupProgram, TM2.stepAux]
    congr 2
    funext tape
    cases tape <;> simp [moved, emitTapes, tokenBits, tokenWords, Token.words,
      encodeWords, encodeWord, haddress, List.reverse_append, List.append_assoc]
  have total := trace_trans _ (trace_trans _ lookup tag) move
  have result := trace_trans _ total finish
  have time : ((MachinePreservingLookupClean.steps input.roots address + 1) +
      (wire + 1 + 1)) + 1 =
      MachinePreservingLookupClean.steps input.roots address + rootLookup input.roots address + 4 := by
    dsimp [wire]
    omega
  rw [time] at result
  exact result

theorem lookupTrace (input : Input) (address : Nat)
    (selected : input.roots[address]? = some (rootLookup input.roots address))
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (lookupProgram address)))^[lookupSteps input address]
      (some ⟨some .start, initialState, base⟩) =
      some ⟨none, initialState,
        emitTapes base [.input (rootLookup input.roots address)]⟩ := by
  have haddress := frame.clean .address (by rfl)
  have start : (advance (TM2.step (lookupProgram address)))^[1]
      (some ⟨some .start, initialState, base⟩) =
      some ⟨some (.lookup (.run .copyFirst)), initialState,
        Function.update base .address (encodeWord address)⟩ := by
    change some (TM2.stepAux (lookupProgram address .start) initialState base) = _
    simp [lookupProgram, Reduction.MachineSubstitution.stepAux_pushWord,
      TM2.stepAux, haddress]
  have tail := lookupTailTrace address input address selected base frame
  have h := trace_trans _ start tail
  have time : 1 + (MachinePreservingLookupClean.steps input.roots address +
      rootLookup input.roots address + 4) = lookupSteps input address := by
    unfold lookupSteps
    omega
  rw [time] at h
  exact h

theorem lookupSteps_le (input : Input) (address : Nat)
    (selected : input.roots[address]? = some (rootLookup input.roots address)) :
    lookupSteps input address ≤ 10 * (input.size + 1) := by
  have hl := MachinePreservingLookupClean.steps_le input.roots address _ selected
  have hw := MachineLookupSpec.output_length_le input.roots address _ selected
  rw [encodeWord_length] at hw
  unfold lookupSteps Input.size
  omega

def Emitter.root (valid : Input → Prop) (address : Nat)
    (present : ∀ input, valid input →
      input.roots[address]? = some (rootLookup input.roots address)) :
    Emitter valid (fun input => [.input (rootLookup input.roots address)]) where
  Label := LookupLabel
  finite := inferInstance
  entry := .start
  program := lookupProgram address
  steps input := lookupSteps input address
  constant := 10
  trace input hv base frame := lookupTrace input address (present input hv) base frame
  bound input hv := lookupSteps_le input address (present input hv)

attribute [instance] Selector.finite

theorem testTrace (within : Bool) (p : Position) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (testProgram within p)))^[testSteps within p input]
      (some ⟨some (.position .start), initialState, base⟩) =
      some ⟨none, (((), testPredicate within p input), none), base⟩ := by
  let prepared := Function.update base .position (encodeWord (p.eval input.cursor))
  have hp := frame.clean .position (by rfl)
  have hs := frame.clean .scratch (by rfl)
  have position := PositionMachine.positionTrace .cursor .scratch .position
    (by decide) (by decide) (by decide) p TestLabel.position
    (some (if within then .compare .scan else .atZero)) (testProgram within p)
    (fun _ => rfl) base input.cursor [] (by simpa using frame.cursorWord) hs ((), false) none
  simp only [hp, List.append_nil] at position
  have test : (advance (TM2.step (testProgram within p)))^[
      if within then MachineUnaryLessAt.steps (p.eval input.cursor) input.capacity else 1]
      (some ⟨some (if within then .compare .scan else .atZero), initialState, prepared⟩) =
      some ⟨some .drain, (((), testPredicate within p input), none), prepared⟩ := by
    cases within with
    | false =>
      change some (TM2.stepAux (testProgram false p .atZero) initialState prepared) = _
      cases hv : p.eval input.cursor <;>
        simp [testProgram, testPredicate, TM2.stepAux, prepared, hv, encodeWord,
          List.replicate_succ]
    | true =>
      have hl := frame.clean .saveLeft (by rfl)
      have hr := frame.clean .saveRight (by rfl)
      have cmp := MachineUnaryLessAt.lessThanTrace compareSlots TestLabel.compare
        (some TestLabel.drain) (testProgram true p) (fun _ => rfl) prepared
        (p.eval input.cursor) input.capacity [] []
        (by simp [prepared, compareSlots_apply, compareTape])
        (by simpa [prepared, compareSlots_apply, compareTape] using frame.capacityWord)
        (by simpa [prepared, compareSlots_apply, compareTape] using hl)
        (by simpa [prepared, compareSlots_apply, compareTape] using hr) () false none
      simpa [testPredicate, initialState] using cmp
  have drain := MachineDrain.drainTrace .position TestLabel.drain none
    (testProgram within p) rfl base (encodeWord (p.eval input.cursor))
    ((), testPredicate within p input) none
  have finish : Function.update base .position [] = base := by
    rw [← hp, Function.update_eq_self]
  rw [encodeWord_length, finish] at drain
  exact trace_trans _ (trace_trans _ position test) drain

def Selector.positionTest (within : Bool) (p : Position) : Selector (testPredicate within p) where
  Label := TestLabel
  finite := inferInstance
  entry := .position .start
  program := testProgram within p
  steps := testSteps within p
  constant := 10 + 4 * positionDepth p
  trace := testTrace within p
  bound := testSteps_le within p

def affineProgram (p : Position) (coefficient offset : Nat) :
    AffineLabel → TM2.Stmt Alphabet AffineLabel State
  | .position label => PositionMachine.statement .cursor .scratch .position p
      AffineLabel.position (some .seed) label
  | .seed => MachineUnaryAffineAt.seed .address offset .scan
  | .scan => MachineUnaryAffineAt.scan .position .scratch .address coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .position id false .restore (some .drain)
  | .drain => MachineDrain.drain .position .drain (some (.lookup (.lookup (.run .copyFirst))))
  | .lookup label => MachineSubroutine.statement AffineLabel.lookup none (lookupProgram 0 label)

theorem affineTrace (p : Position) (coefficient offset : Nat) (input : Input)
    (present : input.roots[affineAddress p coefficient offset input]? =
      some (rootLookup input.roots (affineAddress p coefficient offset input)))
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (affineProgram p coefficient offset)))^[affineSteps p coefficient offset input]
      (some ⟨some (.position .start), initialState, base⟩) =
      some ⟨none, initialState, emitTapes base
        [.input (rootLookup input.roots (affineAddress p coefficient offset input))]⟩ := by
  let pos := p.eval input.cursor
  let addr := affineAddress p coefficient offset input
  let prepared := Function.update base .position (encodeWord pos)
  let addressed := Function.update base .address (encodeWord addr)
  have hp := frame.clean .position (by rfl)
  have ha := frame.clean .address (by rfl)
  have hs := frame.clean .scratch (by rfl)
  have position := PositionMachine.positionTrace .cursor .scratch .position
    (by decide) (by decide) (by decide) p AffineLabel.position (some .seed)
    (affineProgram p coefficient offset) (fun _ => rfl) base input.cursor []
    (by simpa using frame.cursorWord) hs ((), false) none
  simp only [hp, List.append_nil] at position
  have address := MachineUnaryAffineAt.seededAffineTrace .position .scratch .address
    (by decide) (by decide) (by decide) coefficient offset AffineLabel.seed
    AffineLabel.scan AffineLabel.restore (some AffineLabel.drain)
    (affineProgram p coefficient offset) rfl rfl rfl prepared pos []
    (by simp [prepared]) (by simpa [prepared] using hs) ((), false) none
  have haddressed : Function.update prepared .address
      (encodeWord (coefficient * pos + offset) ++ prepared .address) =
      Function.update addressed .position (encodeWord pos) := by
    funext tape
    cases tape <;> simp [prepared, addressed, addr, affineAddress, pos, ha]
  rw [haddressed] at address
  have drain := MachineDrain.drainTrace .position AffineLabel.drain
    (some (.lookup (.lookup (.run .copyFirst)))) (affineProgram p coefficient offset)
    rfl addressed (encodeWord pos) ((), false) none
  have hclean : Function.update addressed .position [] = addressed := by
    have h : addressed .position = [] := by simpa [addressed] using hp
    rw [← h, Function.update_eq_self]
  rw [encodeWord_length, hclean] at drain
  have source := lookupTailTrace 0 input addr present base frame
  have lookup := MachineSubroutine.trace AffineLabel.lookup none (lookupProgram 0)
    (affineProgram p coefficient offset) (fun _ => rfl)
    (MachinePreservingLookupClean.steps input.roots addr + rootLookup input.roots addr + 4)
    _ _ source
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at lookup
  exact trace_trans _ (trace_trans _ (trace_trans _ position address) drain) lookup

def Emitter.affineRoot (valid : Input → Prop) (p : Position) (coefficient offset : Nat)
    (present : ∀ input, valid input →
      input.roots[affineAddress p coefficient offset input]? =
        some (rootLookup input.roots (affineAddress p coefficient offset input))) :
    Emitter valid (fun input => [.input
      (rootLookup input.roots (affineAddress p coefficient offset input))]) where
  Label := AffineLabel
  finite := inferInstance
  entry := .position .start
  program := affineProgram p coefficient offset
  steps := affineSteps p coefficient offset
  constant := 30 + 3 * positionDepth p
  trace input hv base frame := affineTrace p coefficient offset input (present input hv) base frame
  bound input hv := affineSteps_le p coefficient offset input (present input hv)

variable {K Λ σ : Type} {Γ : K → Type} [∀ k, DecidableEq (Γ k)]
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def compileCell (indexing : ConfigIndex.Indexing Γ Λ σ) (k : K) (p : Position)
    (symbol : Option (Γ k)) :
    Emitter (RootsValid indexing) (termTokens indexing (.cell k p symbol)) := by
  let leftValid : Input → Prop := fun input =>
    RootsValid indexing input ∧ p.eval input.cursor < input.capacity
  let addressOffset := indexing.labelCount + indexing.stateCount + (indexing.symbols ⟨k, symbol⟩).val
  let left := Emitter.affineRoot leftValid p indexing.symbolCount addressOffset (by
    intro input hv
    apply rootLookup_present indexing input.roots input.capacity hv.1
    simpa only [affineAddress, addressOffset, Nat.mul_comm, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using
      cellAddress_lt_width indexing input.capacity k (p.eval input.cursor) symbol hv.2)
  let right := Emitter.literal (RootsValid indexing) [.const (decide ((none : Option (Γ k)) = symbol))]
  let branch := Emitter.choice (Selector.positionTest true p) left right
    (valid := RootsValid indexing)
    (fun input hv ht => ⟨hv, by simpa [testPredicate] using ht⟩)
    (fun _ hv _ => hv)
  exact branch.congr (fun input => by
    by_cases hp : p.eval input.cursor < input.capacity <;>
      simp [termTokens, Term.tokens, testPredicate, hp, affineAddress, addressOffset,
        Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm])

def compile (indexing : ConfigIndex.Indexing Γ Λ σ) :
    (term : Term Γ σ) → Emitter (RootsValid indexing) (termTokens indexing term)
  | .state v => Emitter.root (RootsValid indexing) (indexing.labelCount + (indexing.states v).val)
      (fun input hv => rootLookup_present indexing input.roots input.capacity hv _
        (stateAddress_lt_width indexing input.capacity v))
  | .cell k p a => compileCell indexing k p a
  | .const b => Emitter.literal (RootsValid indexing) [.const b]
  | .not e => ((compile indexing e).seq (Emitter.literal (RootsValid indexing) [.not])).congr
      (fun input => rfl)
  | .and e f => ((compile indexing e).seq
      ((compile indexing f).seq (Emitter.literal (RootsValid indexing) [.and]))).congr
        (fun input => by simp [termTokens, Term.tokens, List.append_assoc])
  | .or e f => ((compile indexing e).seq
      ((compile indexing f).seq (Emitter.literal (RootsValid indexing) [.or]))).congr
        (fun input => by simp [termTokens, Term.tokens, List.append_assoc])
  | .atZero p yes no =>
      (Emitter.choice (Selector.positionTest false p) (compile indexing yes) (compile indexing no)
        (fun _ hv _ => hv) (fun _ hv _ => hv)).congr
          (fun input => by simp [termTokens, Term.tokens, testPredicate])
  | .within p yes no =>
      (Emitter.choice (Selector.positionTest true p) (compile indexing yes) (compile indexing no)
        (fun _ hv _ => hv) (fun _ hv _ => hv)).congr
          (fun input => by simp [termTokens, Term.tokens, testPredicate])

def compileGlobal (indexing : ConfigIndex.Indexing Γ Λ σ) :
    (term : Global (Γ := Γ) (Λ := Λ) (σ := σ)) →
      Emitter (RootsValid indexing) (globalTokens indexing term)
  | .label label => Emitter.root (RootsValid indexing) (indexing.labels label).val
      (fun input hv => rootLookup_present indexing input.roots input.capacity hv _
        (labelAddress_lt_width indexing input.capacity label))
  | .data term => compile indexing term
  | .const b => Emitter.literal (RootsValid indexing) [.const b]
  | .and e f => ((compileGlobal indexing e).seq
      ((compileGlobal indexing f).seq (Emitter.literal (RootsValid indexing) [.and]))).congr
        (fun input => by simp [globalTokens, Global.tokens, List.append_assoc])
  | .or e f => ((compileGlobal indexing e).seq
      ((compileGlobal indexing f).seq (Emitter.literal (RootsValid indexing) [.or]))).congr
        (fun input => by simp [globalTokens, Global.tokens, List.append_assoc])

end BinPackingGames.Foundations.Complexity.CookLevin.TermMachine

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionArena
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

open StatementCircuit CircuitBatch PostfixModel PostfixAlignment

variable {inputs oldWidth newWidth width : Nat}

theorem initial_tokens_length_le (V : NPVerifier) (input : List Bool) :
    (tokenBits (forestTokens (fun i : Fin (2 * V.witnessBound.eval input.length + 1) => i.val)
      (List.ofFn (VerifierCircuit.initialExpressions V input)))).length ≤
      (tapePolynomial V).eval input.length := by
  rw [tapePolynomial_eval]
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  apply stage_tokenBits_length_le (Frame.initial id)
  · change _ + 0 ≤ _
    omega
  · omega

theorem transition_tokens_length_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t < V.horizon input.length) :
    (tokenBits (forestTokens
      (fun i => ((VerifierCircuit.timeFrame V input t).wires i).val)
      (List.ofFn (VerifierCircuit.stepExpressions V input)))).length ≤
      (tapePolynomial V).eval input.length := by
  rw [tapePolynomial_eval]
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hp := timeFrame_gates_le V input t (Nat.le_of_lt ht)
  have hb := budgetPolynomial_eval V input
  have hm := Nat.mul_le_mul_right
    (Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)))
    (show 1 ≤ V.horizon input.length by omega)
  apply stage_tokenBits_length_le (VerifierCircuit.timeFrame V input t)
  · change _ + _ ≤ _
    omega
  · omega

theorem timeFrame_stageEnvelope (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t < V.horizon input.length) :
    let B := (stageEnvelopePolynomial V).eval input.length
    let f := VerifierCircuit.timeFrame V input t
    VerifierCircuit.capacity V input.length ≤ B ∧ next f ≤ B ∧
    Batch.cost (List.ofFn (VerifierCircuit.stepExpressions V input)) ≤ B ∧
    (snapshot f).rootBits.length ≤ B ∧
    (tokenBits (forestTokens (fun i => (f.wires i).val)
      (List.ofFn (VerifierCircuit.stepExpressions V input)))).length ≤ B := by
  dsimp only
  have hc := timeFrame_current_le V input t (Nat.le_of_lt ht)
  have hcost := transition_cost_le_budget V input (by omega)
  have hr := (timeFrame_lengths_le V input t (Nat.le_of_lt ht)).2.1
  have htoks := transition_tokens_length_le V input t ht
  rw [stageEnvelopePolynomial_eval]
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

section GenericTransition

variable {K Λ σ : Type} {Γ : K → Type}
  [DecidableEq K] [DecidableEq Λ] [DecidableEq σ]
  [Fintype Λ] [Fintype σ] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)]

theorem compile_transitionTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (S : Nat)
    (f : Frame inputs (indexing.width S + 1)) :
    compileTokens (next f) [] (transitionTokens indexing program S (rootValues f)) =
      some (next (f.step (stepExpressions indexing program S)),
        (rootValues (f.step (stepExpressions indexing program S))).reverse,
        Batch.gates (fun i => (f.wires i).val) (next f)
          (List.ofFn (stepExpressions indexing program S))) := by
  rw [transitionTokens_eq]
  have hw : (fun i : Fin (indexing.width S + 1) => (rootValues f)[i.val]?.getD 0) =
      (fun i => (f.wires i).val) := by
    funext i
    unfold rootValues
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt),
      List.getElem_ofFn]
    rfl
  rw [hw]
  exact compile_frameForest f _

end GenericTransition

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerInvariant

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_VerifierFront
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

open Turing MachineComposition
open BinPackingGames.Foundations.Hastad.SourceHeaderCounts
open PolynomialMachine

instance privateFintype (ps : List (Polynomial Nat)) : Fintype (Private ps) := by
  induction ps with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (Fintype (PhasePrivate p ⊕ Private ps))

instance labelFintype (ps : List (Polynomial Nat)) : Fintype (Label ps) := by
  induction ps with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Eval.Label p ⊕ Label ps))

instance labelDecidableEq (ps : List (Polynomial Nat)) : DecidableEq (Label ps) := by
  induction ps with
  | nil => exact inferInstanceAs (DecidableEq Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Eval.Label p ⊕ Label ps))

instance outputFintype (ps : List (Polynomial Nat)) : Fintype (Output ps) := by
  induction ps with
  | nil => exact inferInstanceAs (Fintype Empty)
  | cons p ps ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Unit ⊕ Output ps))

variable {K Λ σ : Type}

theorem head_clean {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (base : K → List Bool) (h : Clean (p :: ps) slots base) :
    MachineHorner.Clean (headSlots slots) base :=
  ⟨h (.inl (.inl 0)), h (.inl (.inl 1)), h (.inl (.inl 3)), h (.inl (.inl 4))⟩

theorem head_coefficients_clean {p : Polynomial Nat} {ps : List (Polynomial Nat)}
    (slots : Layout (p :: ps) ↪ K) (base : K → List Bool) (h : Clean (p :: ps) slots base)
    (i : Fin (width p)) : base (headSlots slots (.inr i)) = [] :=
  h (.inl (.inr i))

variable [DecidableEq K]

def timePolynomial : List (Polynomial Nat) → Polynomial Nat
  | [] => 0
  | p :: ps => PolynomialMachine.timePolynomial p + timePolynomial ps

theorem steps_le_timePolynomial (ps : List (Polynomial Nat)) (n : Nat) :
    steps ps n ≤ (timePolynomial ps).eval n := by
  induction ps with
  | nil => simp [steps, timePolynomial]
  | cons p ps ih =>
    have hp : Eval.steps p n ≤ (PolynomialMachine.timePolynomial p).eval n := by
      rw [PolynomialMachine.timePolynomial_eval]
      unfold Eval.steps
      omega
    simpa only [steps, timePolynomial, Polynomial.eval_add] using Nat.add_le_add hp ih

theorem trace (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (labels : Label ps → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineHorner.State σ))
    (atLabels : ∀ l, program (labels l) = statement ps slots labels exit l)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl ())) = encodeWord n) (clean : Clean ps slots base)
    (ambient : σ) :
    (advance (TM2.step program))^[steps ps n]
      (some ⟨entry ps labels exit, ((ambient, ()), none), base⟩) =
      some ⟨exit, ((ambient, ()), none), resultTapes ps slots base n⟩ := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    have first := Eval.trace p (headSlots slots) (fun l => labels (.inl l))
      (entry ps (fun l => labels (.inr l)) exit) program
      (fun l => atLabels (.inl l)) base n (by simpa using hinput)
      (head_coefficients_clean slots base clean) (head_clean slots base clean) ambient none
    have hnext : MachineHorner.resultTapes (headSlots slots) base (p.eval n)
        (tailSlots slots (.inl ())) = encodeWord n := by
      rw [MachineHorner.resultTapes,
        Function.update_of_ne (head_output_ne_tail slots (.inl ())).symm]
      exact hinput
    have second := ih (tailSlots slots) (fun l => labels (.inr l))
      (fun l => atLabels (.inr l))
      (MachineHorner.resultTapes (headSlots slots) base (p.eval n)) hnext
      (tail_clean_after_head slots base clean (p.eval n))
    exact trace_trans _ first second

theorem programTrace (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl ())) = encodeWord n) (clean : Clean ps slots base)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program ps slots)))^[1 + steps ps n]
      (some ⟨some (.inl ()), ((ambient, ()), register), base⟩) =
      some ⟨none, ((ambient, ()), none), resultTapes ps slots base n⟩ := by
  have first : (advance (TM2.step (program ps slots)))^[1]
      (some ⟨some (.inl ()), ((ambient, ()), register), base⟩) =
      some ⟨entry ps Sum.inr none, ((ambient, ()), none), base⟩ := by
    change some (TM2.stepAux (program ps slots (.inl ())) _ _) = _
    simp only [program, TM2.stepAux]
    cases h : entry ps (Sum.inr : Label ps → ProgramLabel ps) none <;> rfl
  have rest := trace ps slots Sum.inr none (program ps slots) (fun _ => rfl)
    base n hinput clean ambient
  exact trace_trans _ first rest

def programInTime (ps : List (Polynomial Nat)) (slots : Layout ps ↪ K)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl ())) = encodeWord n) (clean : Clean ps slots base)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program ps slots))
      ⟨some (.inl ()), ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes ps slots base n⟩)
      ((1 + timePolynomial ps).eval n) where
  steps := 1 + steps ps n
  evals_in_steps := programTrace ps slots base n hinput clean ambient register
  steps_le_m := by
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.add_le_add_left (steps_le_timePolynomial ps n) 1

def clocksInTime (V : NPVerifier) (slots : Layout (clockPolynomials V) ↪ K)
    (base : K → List Bool) (n : Nat)
    (hinput : base (slots (.inl ())) = encodeWord n)
    (clean : Clean (clockPolynomials V) slots base) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program (clockPolynomials V) slots))
      ⟨some (.inl ()), ((ambient, ()), register), base⟩
      (some ⟨none, ((ambient, ()), none), resultTapes (clockPolynomials V) slots base n⟩)
      ((1 + timePolynomial (clockPolynomials V)).eval n) :=
  programInTime (clockPolynomials V) slots base n hinput clean ambient register

end BinPackingGames.Foundations.Complexity.CookLevin.ClockPreparation

namespace BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront
open Turing MachineComposition
open BinPackingGames.Foundations.Hastad

variable {A : Type}

theorem uniform_frame_tapes (V : NPVerifier) (word : List Bool) :
    MachineAlphabetTransport.tapes (alphabet_eq V)
      (MachineEmbedding.tapes (InputFrame.tapes word [] []) (fun _ => [])) = frameTapes V word := by
  funext k
  rw [alphabet_tapes_apply]
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr k => rfl

def frameInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (.inl 0), (ambient, none), frameTapes V input⟩
      (some ⟨some (phase V 0), (ambient, none), framedTapes V input⟩)
      (4 * input.length + 7) := by
  have hi : initList InputFrame.machine input = InputFrame.cfg (some 0) input [] [] := by
    unfold initList InputFrame.cfg
    congr 1
    funext i
    fin_cases i <;> simp [InputFrame.machine, InputFrame.tapes]
  let original : StateTransition.EvalsToInTime (TM2.step InputFrame.program)
      (InputFrame.cfg (some 0) input [] [])
      (some (InputFrame.cfg none (encodeWord input.length ++ input) [] []))
      (4 * input.length + 7) := {
    steps := 4 * input.length + 7
    evals_in_steps := by
      rw [← hi, InputFrame.stopped_eq_haltList]
      exact InputFrame.frameTrace input
    steps_le_m := le_rfl }
  have em := embeddedExecution (some (phase V 0)) ambient (fun _ => [])
    InputFrame.program (innerExtra V) original
  have st := MachineStateEquiv.execution (frameStates A) (embeddedProgram V) em
  have result := MachineAlphabetTransport.executionInTime (alphabet_eq V)
    (MachineStateEquiv.program (frameStates A) (embeddedProgram V)) st
  simpa only [program, InputFrame.cfg, MachineAlphabetTransport.configuration_mk,
    MachineStateEquiv.configuration, MachineEmbedding.configuration, MachineEmbedding.label,
    Option.map_some, frameStates, Equiv.coe_fn_mk, uniform_frame_tapes, framedTapes] using result

def copyInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (phase V 0), (ambient, none), framedTapes V input⟩
      (some ⟨some (phase V 2), (ambient, none), copiedTapes V input⟩)
      (4 * input.length + 4) := by
  have run := MachineCopy.copyInTime (raw V) (stream V) (scratch V)
    (by simp [raw, stream]) (by simp [raw, scratch]) (by simp [stream, scratch])
    false (phase V 0) (phase V 1) (some (phase V 2)) (program V)
    (by simp [phase, extraProgram]) (by simp [phase, extraProgram])
    (framedTapes V input) (by simp [framedTapes, frameTapes, scratch]) ambient none
  have hb : 2 * ((framedTapes V input (raw V)).length + 1) = 4 * input.length + 4 := by
    simp only [framedTapes, frameTapes, raw, ite_true, if_true, List.length_append, encodeWord_length]
    omega
  rw [hb] at run
  simpa [framedTapes, frameTapes, raw, stream, copiedTapes] using run

def fieldInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (phase V 2), (ambient, none), copiedTapes V input⟩
      (some ⟨some (clockLabel V (.inl ())), (ambient, none), seedTapes V input⟩)
      (input.length + 2) := by
  have run := SourceMachine.fieldInTime (raw V) (lengthTape V)
    (by simp [raw, lengthTape, clockSlots]) (phase V 2) (phase V 3)
    (some (clockLabel V (.inl ()))) (program V)
    (by simp [phase, extraProgram]) (by simp [phase, extraProgram])
    (copiedTapes V input) input.length input
    (by simp [copiedTapes, raw, stream, framedTapes, frameTapes]) ambient none
  simpa [SourceMachine.fieldTapes, seedTapes, copiedTapes, lengthTape, clockSlots,
    stream, framedTapes, frameTapes] using run

theorem seed_input (V : NPVerifier) (input : List Bool) :
    seedTapes V input (clockSlots V (.inl ())) = encodeWord input.length := by
  simp [seedTapes, lengthTape]

def clocksInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (clockLabel V (.inl ())), (ambient, none), seedTapes V input⟩
      (some ⟨none, (ambient, none), preparedTapes V input⟩)
      ((1 + ClockPreparation.timePolynomial (ClockPreparation.clockPolynomials V)).eval input.length) := by
  have original := ClockPreparation.clocksInTime V (clockSlots V) (seedTapes V input)
    input.length (seed_input V input) (seed_clean V input) ambient none
  have st := MachineStateEquiv.execution (clockStates A)
    (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V)) original
  have sub := MachineSubroutine.execution (clockLabel V) none
    (MachineStateEquiv.program (clockStates A)
      (ClockPreparation.program (ClockPreparation.clockPolynomials V) (clockSlots V)))
    (program V) (by intro l; simp [clockLabel, extraProgram, MachineStateEquiv.program]) st
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label,
    MachineStateEquiv.configuration, Option.map_some, clockStates, Equiv.coe_fn_mk,
    preparedTapes] using sub

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  Polynomial.C 9 * Polynomial.X + Polynomial.C 14 + ClockPreparation.timePolynomial (ClockPreparation.clockPolynomials V)

def prepareInTime (V : NPVerifier) (input : List Bool) (ambient : A) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (.inl 0), (ambient, none), frameTapes V input⟩
      (some ⟨none, (ambient, none), preparedTapes V input⟩)
      ((timePolynomial V).eval input.length) := by
  let one := frameInTime V input ambient
  let two := copyInTime V input ambient
  let three := fieldInTime V input ambient
  let four := clocksInTime V input ambient
  let a := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ one two
  let b := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ a three
  let c := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ b four
  exact {
    toEvalsTo := c.toEvalsTo
    steps_le_m := by
      have h := c.steps_le_m
      simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one] at *
      omega }

end BinPackingGames.Foundations.Complexity.CookLevin.VerifierFront

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_ProducerFrontStage
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

theorem trace (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = statement p labels exit l)
    (base : K → List Bool) (free : Nat) (ready : Ready p base free)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[2 * free + 5]
      (some ⟨some (labels .copy), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), prepared p base⟩ := by
  have hc := MachineCopy.copyTrace (p 0) (p 1) (p 2)
    (p.injective.ne (by decide : (0 : Fin 5) ≠ 1))
    (p.injective.ne (by decide : (0 : Fin 5) ≠ 2))
    (p.injective.ne (by decide : (1 : Fin 5) ≠ 2))
    false (labels .copy) (labels .restore) (some (labels .seed))
    program (code .copy) (code .restore) base ready.scratch ambient register
  have hs := seedTrace p labels exit program (code .seed) base ambient
  have time : 2 * free + 5 = 1 + 2 * ((base (p 0)).length + 1) := by
    rw [ready.source, encodeWord_length]
    omega
  rw [time, Function.iterate_add_apply, hc]
  exact hs

def inTime (p : Ports K) (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = statement p labels exit l)
    (base : K → List Bool) (free : Nat) (ready : Ready p base free)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .copy), (ambient, register), base⟩
      (some ⟨exit, (ambient, none), prepared p base⟩) (2 * free + 5) where
  steps := 2 * free + 5
  evals_in_steps := by
    change (advance (TM2.step program))^[2 * free + 5] _ = _
    exact trace p labels exit program code base free ready ambient register
  steps_le_m := le_rfl

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerBootstrap

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssemblyBounds

open Polynomial

local instance instDecidableEqΓTmBoolComputation_r3fb9fa_1 (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
def cellsPolynomial (V : NPVerifier) : Polynomial Nat :=
  let A := (VerifierCircuit.indexing V).symbolCount
  let q := V.witnessBound
  let s := Bounds.capacityPolynomial V.computation.time q
    (Runtime.programPushBound V.computation.tm)
  (2 * (s + 2) + (C (A + 4) * (2 * X + 1) + 3)) + (2 * (q + 2) + 1) +
    (q * (C A * (120 * (q + 2)^2 + 1) + 3) + 1) + (s + 1) + (q + 3)

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  1 + cellsPolynomial V + ValidityMachine.Full.timePolynomial.comp V.witnessBound

theorem capacityPolynomial_eval (V : NPVerifier) (n : Nat) :
    (Bounds.capacityPolynomial V.computation.time V.witnessBound
      (Runtime.programPushBound V.computation.tm)).eval n = VerifierCircuit.capacity V n := by
  simp [VerifierCircuit.capacity, NPVerifier.horizon, Nat.mul_comm]

theorem cellsPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (cellsPolynomial V).eval input.length =
      (2 * (VerifierCircuit.capacity V input.length + 2) +
        (((VerifierCircuit.indexing V).symbolCount + 4) * (WitnessEncoding.inputPrefix input).length + 3)) +
      (2 * (V.witnessBound.eval input.length + 2) + 1) +
      (V.witnessBound.eval input.length * ((VerifierCircuit.indexing V).symbolCount *
        (120 * (V.witnessBound.eval input.length + 2)^2 + 1) + 3) + 1) +
      (VerifierCircuit.capacity V input.length + 1) + (V.witnessBound.eval input.length + 3) := by
  simp only [cellsPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    Polynomial.eval_one, capacityPolynomial_eval, WitnessEncoding.inputPrefix_length]

theorem cells_steps_le (V : NPVerifier) (input : List Bool) :
    CellsMachine.steps (PayloadCellsMachine.symbolTable V) (WitnessEncoding.inputPrefix input).length
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) ≤
      (cellsPolynomial V).eval input.length := by
  rw [cellsPolynomial_eval]
  exact CellsMachine.steps_le (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length)

theorem steps_le (V : NPVerifier) (input : List Bool) :
    1 + CellsMachine.steps (PayloadCellsMachine.symbolTable V) (WitnessEncoding.inputPrefix input).length
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) +
      ValidityMachine.Full.steps (V.witnessBound.eval input.length) ≤
      (timePolynomial V).eval input.length := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_comp]
  exact Nat.add_le_add (Nat.add_le_add_left (cells_steps_le V input) 1)
    (ValidityMachine.Full.steps_le_time (V.witnessBound.eval input.length))

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssemblyBounds

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly

open Turing PostfixModel

open MachineComposition
open ClashMachine (State clean emitted)

abbrev Label (V : NPVerifier) := CodeLabel (VerifierCircuit.indexing V).symbolCount

variable {K Λ σ : Type} [DecidableEq K]

def cellsLabels {V : NPVerifier} (labels : Label V ↪ Λ) :
    CellsMachine.Label (VerifierCircuit.indexing V).symbolCount ↪ Λ :=
  ⟨fun l => labels (.cells l), fun _ _ h => CodeLabel.cells.inj (labels.injective h)⟩

structure Ready (V : NPVerifier) (slots : Tape 9 ↪ K) (base : K → List Bool)
    (input : List Bool) : Prop where
  rawWord : base (slots .rawInput) = input
  framedWord : base (slots .framedInput) = WitnessEncoding.inputPrefix input
  boundWord : base (slots .witnessBound) = encodeWord (V.witnessBound.eval input.length)
  capacityWord : base (slots .capacity) = encodeWord (VerifierCircuit.capacity V input.length)
  cellEmpty : ∀ j, base (slots (.cellWork j)) = []
  validityEmpty : ∀ j, base (slots (.validityWork j)) = []

theorem Ready.afterEmitted {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input)
    (ts : List Token) :
    Ready V slots (emitted (slots .reversed) (slots .count) base ts) input := by
  constructor
  · simpa [emitted, slots.injective.eq_iff] using ready.rawWord
  · simpa [emitted, slots.injective.eq_iff] using ready.framedWord
  · simpa [emitted, slots.injective.eq_iff] using ready.boundWord
  · simpa [emitted, slots.injective.eq_iff] using ready.capacityWord
  · intro j
    simpa [emitted, slots.injective.eq_iff] using ready.cellEmpty j
  · intro j
    simpa [emitted, slots.injective.eq_iff] using ready.validityEmpty j

omit [DecidableEq K] in
theorem Ready.cellsReady {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input) :
    CellsMachine.Ready (cellsSlots.trans slots) base (WitnessEncoding.inputPrefix input)
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) := by
  constructor
  · exact ready.framedWord
  · exact ready.boundWord
  · exact ready.capacityWord
  · intro j hj
    fin_cases j <;> simp_all [cellsSlots, ready.cellEmpty]

omit [DecidableEq K] in
theorem Ready.validityReady {V : NPVerifier} {slots : Tape 9 ↪ K}
    {base : K → List Bool} {input : List Bool} (ready : Ready V slots base input) :
    ClashMachine.Full.Ready ((validitySlots 9).trans slots) base
      (V.witnessBound.eval input.length) := by
  constructor
  · exact ready.boundWord
  · intro j hj ho hc
    fin_cases j <;> simp_all [ready.validityEmpty]

theorem capacity_within (V : NPVerifier) (input : List Bool) :
    (WitnessEncoding.inputPrefix input).length + V.witnessBound.eval input.length ≤
      VerifierCircuit.capacity V input.length := by
  simp only [WitnessEncoding.inputPrefix_length, VerifierCircuit.capacity]
  omega

def statement (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) : Label V → TM2.Stmt (fun _ : K => Bool) Λ (State σ)
  | .control => InitializationControl.statement V (placedControl slots)
      (some (labels (.cells (.prefix .capacityFirst))))
  | .cells l => CellsMachine.statement (cellsSlots.trans slots) (cellsLabels labels)
      (some (labels (.validity (.nonempty .initialize_))))
      (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
      (PaddingCellsMachine.blankRow V) l
  | .validity l => ValidityMachine.Full.statement ((validitySlots 9).trans slots)
      (fun l => labels (.validity l)) exit l

def Agrees (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ)) : Prop :=
  ∀ l, program (labels l) = statement V slots labels exit l

def steps (V : NPVerifier) (input : List Bool) : Nat :=
  1 + CellsMachine.steps (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length) +
    ValidityMachine.Full.steps (V.witnessBound.eval input.length)

theorem cellsTokens_eq (V : NPVerifier) (input : List Bool) :
    CellsMachine.tokens (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
      (PaddingCellsMachine.blankRow V) (WitnessEncoding.inputPrefix input)
      (V.witnessBound.eval input.length) (VerifierCircuit.capacity V input.length) =
      InitializationControl.cells V input (VerifierCircuit.capacity V input.length) :=
  CellsTokensAlignment.cells_eq_streams V input (VerifierCircuit.capacity V input.length)
    (capacity_within V input)

theorem trace (V : NPVerifier) (slots : Tape 9 ↪ K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V slots labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : Ready V slots base input) (ambient : σ) :
    (advance (TM2.step program))^[steps V input]
      (some ⟨some (labels .control), clean ambient, base⟩) =
      some ⟨exit, clean ambient, emitted (slots .reversed) (slots .count) base
        (InitializationTemplate.initializationTokens V input)⟩ := by
  let first := InitializationControl.tokens V
  let middle := InitializationControl.cells V input (VerifierCircuit.capacity V input.length)
  let b₁ := emitted (slots .reversed) (slots .count) base first
  let b₂ := emitted (slots .reversed) (slots .count) b₁ middle
  have h₁ := InitializationControl.trace V (placedControl slots) (labels .control)
    (some (labels (.cells (.prefix .capacityFirst)))) program (ha .control) base (clean ambient)
  change (advance (TM2.step program))^[1]
    (some ⟨some (labels .control), clean ambient, base⟩) =
    some ⟨some (labels (.cells (.prefix .capacityFirst))), clean ambient, b₁⟩ at h₁
  have h₂ := CellsMachine.trace (cellsSlots.trans slots) (cellsLabels labels)
    (some (labels (.validity (.nonempty .initialize_))))
    (InputCellsMachine.prefixTruth V) (PayloadCellsMachine.symbolTable V)
    (PaddingCellsMachine.blankRow V) program (fun l => ha (.cells l)) b₁
    (WitnessEncoding.inputPrefix input) (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length) (capacity_within V input)
    (ready.afterEmitted first).cellsReady ambient
  rw [cellsTokens_eq] at h₂
  change (advance (TM2.step program))^[CellsMachine.steps (PayloadCellsMachine.symbolTable V)
    (WitnessEncoding.inputPrefix input).length (V.witnessBound.eval input.length)
    (VerifierCircuit.capacity V input.length)]
    (some ⟨some (labels (.cells (.prefix .capacityFirst))), clean ambient, b₁⟩) =
    some ⟨some (labels (.validity (.nonempty .initialize_))), clean ambient, b₂⟩ at h₂
  have h₃ := ValidityMachine.Full.trace ((validitySlots 9).trans slots)
    (fun l => labels (.validity l)) exit program (fun l => ha (.validity l)) b₂
    (V.witnessBound.eval input.length)
    ((ready.afterEmitted first).afterEmitted middle).validityReady ambient
  have h := ClashMachine.chain (ClashMachine.chain h₁ h₂) h₃
  simpa only [steps, b₂, b₁, first, middle,
    show ((validitySlots 9).trans slots) 7 = slots .reversed from rfl,
    show ((validitySlots 9).trans slots) 8 = slots .count from rfl,
    ClashMachine.emitted_append (slots .reversed) (slots .count)
      (slots.injective.ne (by decide : (Tape.reversed : Tape 9) ≠ .count)),
    InitializationControl.initializationTokens_eq_blocks] using h

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  InitializationAssemblyBounds.timePolynomial V

theorem steps_le_timePolynomial (V : NPVerifier) (input : List Bool) :
    steps V input ≤ (timePolynomial V).eval input.length :=
  InitializationAssemblyBounds.steps_le V input

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationAssembly

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

open Turing

abbrev Alphabet (V : NPVerifier) (_ : Tape V) := Bool

def forestPorts (V : NPVerifier) : ForestStage.Tape ↪ Tape V :=
  TransitionArena.forestPorts.trans (transitionPorts V)

def empty (V : NPVerifier) : Tape V → List Bool := fun _ => []

theorem front_fill (V : NPVerifier) (contents : VerifierFront.Tape V → List Bool) :
    ForestPlacement.fill (frontPorts V) (empty V) contents = frontTapes V contents := by
  funext t
  cases t with
  | inl t => exact ForestPlacement.fill_at (frontPorts V) (empty V) contents t
  | inr t =>
    exact ForestPlacement.fill_other (frontPorts V) (empty V) contents _
      (by intro i; simp [frontPorts])

def initialTapes (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  frontTapes V (VerifierFront.frameTapes V input)

theorem initialTapes_eq (V : NPVerifier) (input : List Bool) :
    initialTapes V input = fun t => if t = raw V then input else [] := by
  funext t
  cases t with
  | inl t =>
    cases t with
    | inl i => fin_cases i <;> simp [initialTapes, frontTapes, VerifierFront.frameTapes,
        raw, VerifierFront.raw]
    | inr t => simp [initialTapes, frontTapes, VerifierFront.frameTapes, raw, VerifierFront.raw]
  | inr t => simp [initialTapes, frontTapes, raw]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionIteration
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionMachine

open Turing MachineComposition TransitionTemplate TermMachine PostfixModel

variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def compileList (indexing : ConfigIndex.Indexing Γ Λ σ) :
    (terms : List (Template (Γ := Γ) (Λ := Λ) (σ := σ))) →
      Emitter (RootsValid indexing) (listTokens indexing terms)
  | [] => (Emitter.literal (RootsValid indexing) []).congr (fun _ => rfl)
  | term :: terms => ((compileGlobal indexing term).seq (compileList indexing terms)).congr
      (fun _ => rfl)

def compilePrefix (indexing : ConfigIndex.Indexing Γ Λ σ) :
    (terms : List (Template (Γ := Γ) (Λ := Λ) (σ := σ) × Bool)) →
      Emitter (RootsValid indexing) (prefixTokens indexing terms)
  | [] => (Emitter.literal (RootsValid indexing) []).congr (fun _ => rfl)
  | term :: terms =>
      (((compileGlobal indexing term.1).seq
        (Emitter.literal (RootsValid indexing) (if term.2 then [.not] else []))).seq
          (compilePrefix indexing terms)).congr (fun _ => rfl)

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem Valid.roots {indexing : ConfigIndex.Indexing Γ Λ σ}
    {plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)} {input : Input}
    (h : Valid indexing plan input) : RootsValid indexing input := by
  unfold Valid at h
  unfold RootsValid
  omega

def finalEmitter (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) :
    Emitter (finalValid indexing plan) (finalTokens indexing plan) := by
  cases hc : plan.carry with
  | false =>
      exact (Emitter.literal (finalValid indexing plan) []).congr (fun input => by
        simp [finalTokens, hc])
  | true =>
      let emitter := Emitter.affineRoot (finalValid indexing plan) .current indexing.symbolCount
        (indexing.labelCount + indexing.stateCount) (by
          intro input hv
          have haddr : affineAddress .current indexing.symbolCount
              (indexing.labelCount + indexing.stateCount) input = indexing.width input.capacity := by
            simp [affineAddress, Position.eval, hv.2, ConfigIndex.Indexing.width,
              Nat.mul_comm, Nat.add_comm, Nat.add_assoc]
          have hlt : indexing.width input.capacity < input.roots.length := by
            have h := hv.1
            simp only [Valid, hc, ite_true, if_true] at h
            omega
          rw [haddr]
          simp only [rootLookup, List.getElem?_eq_getElem hlt, Option.getD_some])
      exact emitter.congr (fun input => by simp [finalTokens, hc])

def guard : Selector (testPredicate true .current) := Selector.positionTest true .current

inductive Label (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ))
  | prefix (label : (compilePrefix indexing plan.prefix).Label)
  | test (label : guard.Label)
  | dispatch
  | cells (label : (compileList indexing plan.cells).Label)
  | increment
  | finishTokens (label : (finalEmitter indexing plan).Label)
  | drain | finish
  deriving Fintype

attribute [-instance] instFintypeLabel

instance labelFintype (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Fintype (Label indexing plan) :=
  Fintype.ofEquiv
    ((compilePrefix indexing plan.prefix).Label ⊕ guard.Label ⊕ Unit ⊕
      (compileList indexing plan.cells).Label ⊕ Unit ⊕ (finalEmitter indexing plan).Label ⊕ Unit ⊕ Unit)
    (Label.proxyTypeEquiv indexing plan)

def program (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) :
    Label indexing plan → TM2.Stmt Alphabet (Label indexing plan) State
  | .prefix label => MachineSubroutine.statement Label.prefix (some (.test guard.entry))
      ((compilePrefix indexing plan.prefix).program label)
  | .test label => MachineSubroutine.statement Label.test (some .dispatch) (guard.program label)
  | .dispatch => .branch (fun state => state.1.2)
      (.load (fun _ => initialState) (.goto fun _ => .cells (compileList indexing plan.cells).entry))
      (.load (fun _ => initialState) (.goto fun _ => .finishTokens (finalEmitter indexing plan).entry))
  | .cells label => MachineSubroutine.statement Label.cells (some .increment)
      ((compileList indexing plan.cells).program label)
  | .increment => .push .cursor (fun _ => true) (.goto fun _ => .test guard.entry)
  | .finishTokens label => MachineSubroutine.statement Label.finishTokens (some .drain)
      ((finalEmitter indexing plan).program label)
  | .drain => MachineDrain.drain .cursor .drain (some .finish)
  | .finish => .push .cursor (fun _ => false) (.load (fun _ => initialState) .halt)

def cellTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) (cursor : Nat) : List Token :=
  listTokens indexing plan.cells (withCursor input cursor)

def remainingTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Nat → Nat → List Token
  | cursor, 0 => finalTokens indexing plan (withCursor input cursor)
  | cursor, remaining + 1 => cellTokens indexing plan input cursor ++
      remainingTokens indexing plan input (cursor + 1) remaining

def loopSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Nat → Nat → Nat
  | cursor, 0 => guard.steps (withCursor input cursor) + 1 +
      (finalEmitter indexing plan).steps (withCursor input cursor) + (cursor + 2) + 1
  | cursor, remaining + 1 => guard.steps (withCursor input cursor) + 1 +
      (compileList indexing plan.cells).steps (withCursor input cursor) + 1 +
      loopSteps indexing plan input (cursor + 1) remaining

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem guardTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (program indexing plan)))^[guard.steps input]
      (some ⟨some (.test guard.entry), initialState, base⟩) =
      some ⟨some .dispatch, (((), decide (input.cursor < input.capacity)), none), base⟩ := by
  have h := MachineSubroutine.trace Label.test (some Label.dispatch) guard.program
    (program indexing plan) (fun _ => rfl) (guard.steps input) _ _
    (guard.trace input base frame)
  simpa [MachineSubroutine.configuration, MachineSubroutine.label, testPredicate, Position.eval]
    using! h

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem dispatchTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (base : Tape → List Bool) (decision : Bool) :
    (advance (TM2.step (program indexing plan)))^[1]
      (some ⟨some .dispatch, (((), decision), none), base⟩) =
      some ⟨some (if decision then .cells (compileList indexing plan.cells).entry
        else .finishTokens (finalEmitter indexing plan).entry), initialState, base⟩ := by
  cases decision <;> rfl

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem incrementTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (program indexing plan)))^[1]
      (some ⟨some .increment, initialState, base⟩) =
      some ⟨some (.test guard.entry), initialState, cursorTapes base (input.cursor + 1)⟩ := by
  have hw : true :: base .cursor = encodeWord (input.cursor + 1) := by
    rw [frame.cursorWord]
    simp [encodeWord, List.replicate_succ]
  change some (TM2.stepAux (program indexing plan .increment) initialState base) = _
  simp [program, TM2.stepAux, cursorTapes, hw]

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem resetTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (program indexing plan)))^[input.cursor + 3]
      (some ⟨some .drain, initialState, base⟩) =
      some ⟨none, initialState, cursorTapes base 0⟩ := by
  have drain := MachineDrain.drainTrace .cursor Label.drain (some Label.finish)
    (program indexing plan) rfl base (encodeWord input.cursor) ((), false) none
  have heq : Function.update base .cursor (encodeWord input.cursor) = base := by
    rw [← frame.cursorWord, Function.update_eq_self]
  rw [heq, encodeWord_length] at drain
  have finish : (advance (TM2.step (program indexing plan)))^[1]
      (some ⟨some .finish, initialState, Function.update base .cursor []⟩) =
      some ⟨none, initialState, cursorTapes base 0⟩ := by
    change some (TM2.stepAux (program indexing plan .finish) initialState _) = _
    simp [program, TM2.stepAux, cursorTapes, encodeWord]
  simpa [Nat.add_assoc, initialState] using trace_trans _ drain finish

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem loopTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) (cursor remaining : Nat)
    (hcapacity : cursor + remaining = input.capacity)
    (base : Tape → List Bool) (frame : Frame (withCursor input cursor) base) :
    (advance (TM2.step (program indexing plan)))^[loopSteps indexing plan input cursor remaining]
      (some ⟨some (.test guard.entry), initialState, base⟩) =
      some ⟨none, initialState,
        cursorTapes (emitTapes base (remainingTokens indexing plan input cursor remaining)) 0⟩ := by
  induction remaining generalizing cursor base with
  | zero =>
      have hc : cursor = input.capacity := by omega
      have hg := guardTrace indexing plan (withCursor input cursor) base frame
      have hd := dispatchTrace indexing plan base false
      have hfalse : decide ((withCursor input cursor).cursor <
          (withCursor input cursor).capacity) = false := by simp [hc]
      rw [hfalse] at hg
      simp only [Bool.false_eq_true, ite_false] at hd
      have hv : finalValid indexing plan (withCursor input cursor) := ⟨valid.withCursor cursor, hc⟩
      have hf := (finalEmitter indexing plan).traceAt Label.finishTokens (some Label.drain)
        (program indexing plan) (fun _ => rfl) (withCursor input cursor) hv base frame
      have hr := resetTrace indexing plan (withCursor input cursor)
        (emitTapes base (finalTokens indexing plan (withCursor input cursor)))
        (frame.emit (finalTokens indexing plan (withCursor input cursor)))
      have total := trace_trans _ (trace_trans _ (trace_trans _ hg hd) hf) hr
      simpa only [loopSteps, remainingTokens, withCursor_cursor, Nat.add_assoc] using total
  | succ remaining ih =>
      have hc : cursor < input.capacity := by omega
      have hg := guardTrace indexing plan (withCursor input cursor) base frame
      have hd := dispatchTrace indexing plan base true
      have htrue : decide ((withCursor input cursor).cursor <
          (withCursor input cursor).capacity) = true := by simp [hc]
      rw [htrue] at hg
      simp only [ite_true, if_true] at hd
      have hb := (compileList indexing plan.cells).traceAt Label.cells (some Label.increment)
        (program indexing plan) (fun _ => rfl) (withCursor input cursor)
        (valid.withCursor cursor).roots base frame
      have hi := incrementTrace indexing plan (withCursor input cursor)
        (emitTapes base (cellTokens indexing plan input cursor))
        (frame.emit (cellTokens indexing plan input cursor))
      have hn := ih (cursor + 1) (by omega)
        (cursorTapes (emitTapes base (cellTokens indexing plan input cursor)) (cursor + 1))
        (by simpa only [withCursor_withCursor] using
          Frame.cursor (frame.emit (cellTokens indexing plan input cursor)) (cursor + 1))
      have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _ hg hd) hb) hi) hn
      simpa only [loopSteps, remainingTokens, cellTokens, withCursor_cursor,
        emitTapes_cursor, cursorTapes_twice, emitTapes_append, Nat.add_assoc] using total

def outputTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  prefixTokens indexing plan.prefix (withCursor input 0) ++
    remainingTokens indexing plan input 0 input.capacity

def steps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Nat :=
  (compilePrefix indexing plan.prefix).steps (withCursor input 0) +
    loopSteps indexing plan input 0 input.capacity

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem fullTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) (base : Tape → List Bool)
    (frame : Frame (withCursor input 0) base) :
    (advance (TM2.step (program indexing plan)))^[steps indexing plan input]
      (some ⟨some (.prefix (compilePrefix indexing plan.prefix).entry), initialState, base⟩) =
      some ⟨none, initialState, emitTapes base (outputTokens indexing plan input)⟩ := by
  have hp := (compilePrefix indexing plan.prefix).traceAt Label.prefix (some (.test guard.entry))
    (program indexing plan) (fun _ => rfl) (withCursor input 0)
    (valid.withCursor 0).roots base frame
  have hl := loopTrace indexing plan input valid 0 input.capacity (by omega)
    (emitTapes base (prefixTokens indexing plan.prefix (withCursor input 0)))
    (frame.emit (prefixTokens indexing plan.prefix (withCursor input 0)))
  have hc : cursorTapes base 0 = base := cursorTapes_same frame
  simpa only [steps, emitTapes_append, ← emitTapes_cursor, hc, outputTokens]
    using trace_trans _ hp hl

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem traceAt {Caller : Type} (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ))
    (labels : Label indexing plan → Caller) (exit : Option Caller)
    (target : Caller → TM2.Stmt Alphabet Caller State)
    (code : ∀ label, target (labels label) =
      MachineSubroutine.statement labels exit (program indexing plan label))
    (input : Input) (valid : Valid indexing plan input) (base : Tape → List Bool)
    (frame : Frame (withCursor input 0) base) :
    (advance (TM2.step target))^[steps indexing plan input]
      (some ⟨some (labels (.prefix (compilePrefix indexing plan.prefix).entry)), initialState, base⟩) =
      some ⟨exit, initialState, emitTapes base (outputTokens indexing plan input)⟩ := by
  have h := MachineSubroutine.trace labels exit (program indexing plan) target code
    (steps indexing plan input) _ _ (fullTrace indexing plan input valid base frame)
  simpa only [MachineSubroutine.configuration, MachineSubroutine.label] using h

def loopConstant (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Nat :=
  guard.constant + (compileList indexing plan.cells).constant +
    (finalEmitter indexing plan).constant + 5

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem loopSteps_le (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) (cursor remaining : Nat)
    (hcapacity : cursor + remaining = input.capacity) :
    loopSteps indexing plan input cursor remaining ≤
      (remaining + 1) * loopConstant indexing plan *
        (2 * input.capacity + (encodeWords input.roots).length + 1) := by
  let B := 2 * input.capacity + (encodeWords input.roots).length + 1
  have hB : 1 ≤ B := by dsimp [B]; omega
  induction remaining generalizing cursor with
  | zero =>
      have hc : cursor = input.capacity := by omega
      have hs : (withCursor input cursor).size + 1 ≤ B := by simp [Input.size, B]; omega
      have hg := guard.bound (withCursor input cursor)
      have hf := (finalEmitter indexing plan).bound (withCursor input cursor)
        ⟨valid.withCursor cursor, hc⟩
      have hg' := hg.trans (Nat.mul_le_mul_left guard.constant hs)
      have hf' := hf.trans (Nat.mul_le_mul_left (finalEmitter indexing plan).constant hs)
      have hcB : cursor ≤ B := by dsimp [B]; omega
      simp only [loopSteps, Nat.zero_add, Nat.one_mul]
      change _ ≤ loopConstant indexing plan * B
      dsimp [loopConstant]
      nlinarith [Nat.zero_le ((compileList indexing plan.cells).constant * B)]
  | succ remaining ih =>
      have hc : cursor ≤ input.capacity := by omega
      have hs : (withCursor input cursor).size + 1 ≤ B := by simp [Input.size, B]; omega
      have hg := guard.bound (withCursor input cursor)
      have hb := (compileList indexing plan.cells).bound (withCursor input cursor)
        (valid.withCursor cursor).roots
      have hg' := hg.trans (Nat.mul_le_mul_left guard.constant hs)
      have hb' := hb.trans (Nat.mul_le_mul_left (compileList indexing plan.cells).constant hs)
      have hi := ih (cursor + 1) (by omega)
      simp only [loopSteps]
      have hstep : guard.steps (withCursor input cursor) + 1 +
          (compileList indexing plan.cells).steps (withCursor input cursor) + 1 ≤
          loopConstant indexing plan * B := by
        dsimp [loopConstant]
        nlinarith [Nat.zero_le ((finalEmitter indexing plan).constant * B)]
      calc
        _ ≤ loopConstant indexing plan * B + (remaining + 1) * loopConstant indexing plan * B :=
          Nat.add_le_add hstep hi
        _ = _ := by dsimp [B]; ring

def timeConstant (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Nat :=
  2 * ((compilePrefix indexing plan.prefix).constant + loopConstant indexing plan)

noncomputable def timePolynomial (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Polynomial Nat :=
  Polynomial.C (timeConstant indexing plan) * (Polynomial.X + 1)^2

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem steps_le (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing plan input) :
    steps indexing plan input ≤ timeConstant indexing plan * (dataSize input + 1)^2 := by
  have hp := (compilePrefix indexing plan.prefix).bound (withCursor input 0)
    (valid.withCursor 0).roots
  have hl := loopSteps_le indexing plan input valid 0 input.capacity (by omega)
  have hcap : input.capacity + 1 ≤ dataSize input + 1 := by simp [dataSize]
  have hdata : 2 * input.capacity + (encodeWords input.roots).length + 1 ≤
      2 * (dataSize input + 1) := by unfold dataSize; omega
  have hmul := Nat.mul_le_mul hcap hdata
  have hp' : (compilePrefix indexing plan.prefix).steps (withCursor input 0) ≤
      (compilePrefix indexing plan.prefix).constant * (dataSize input + 1) := by
    simpa [withCursor, Input.size, dataSize] using hp
  have hprod := Nat.mul_le_mul_left (loopConstant indexing plan) hmul
  have hsq : dataSize input + 1 ≤ (dataSize input + 1)^2 := by nlinarith
  have hprefix := Nat.mul_le_mul_left (compilePrefix indexing plan.prefix).constant hsq
  unfold steps timeConstant
  nlinarith

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem remainingTokens_eq_range (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) (cursor remaining : Nat) :
    remainingTokens indexing plan input cursor remaining =
      ((List.range' cursor remaining).flatMap (cellTokens indexing plan input)) ++
        finalTokens indexing plan (withCursor input (cursor + remaining)) := by
  induction remaining generalizing cursor with
  | zero => simp [remainingTokens]
  | succ remaining ih =>
      simp [remainingTokens, List.range'_succ, ih, List.append_assoc,
        Nat.add_comm, Nat.add_left_comm]

def carriedTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  if plan.carry then [.input (rootLookup input.roots (indexing.width input.capacity))] else []

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem finalTokens_at_capacity (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) :
    finalTokens indexing plan (withCursor input input.capacity) = carriedTokens indexing plan input := by
  simp [finalTokens, carriedTokens, affineAddress, Position.eval,
    ConfigIndex.Indexing.width, Nat.mul_comm, Nat.add_comm, Nat.add_assoc]

omit [DecidableEq K] [Fintype σ] [DecidableEq σ] [(tape : K) → DecidableEq (Γ tape)]
  [(tape : K) → Fintype (Γ tape)] [DecidableEq Λ] [Fintype Λ] in
theorem outputTokens_eq_blocks (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) :
    outputTokens indexing plan input =
      prefixTokens indexing plan.prefix (withCursor input 0) ++
      ((List.finRange input.capacity).flatMap fun cursor =>
        cellTokens indexing plan input cursor.val) ++ carriedTokens indexing plan input := by
  rw [outputTokens, remainingTokens_eq_range]
  simp only [Nat.zero_add, finalTokens_at_capacity]
  rw [← List.range_eq_range', ← List.map_coe_finRange_eq_range, List.flatMap_map]
  simp only [List.append_assoc]

def transitionPrefixKinds (indexing : ConfigIndex.Indexing Γ Λ σ) : List (OutputKind Γ Λ σ) :=
  ((List.finRange indexing.labelCount).map fun i => .inl (indexing.labels.symm i)) ++
    ((List.finRange indexing.stateCount).map fun i => .inr (.inl (indexing.states.symm i)))

def transitionCellKinds (indexing : ConfigIndex.Indexing Γ Λ σ) : List (OutputKind Γ Λ σ) :=
  (List.finRange indexing.symbolCount).map fun i => .inr (.inr (indexing.symbols.symm i))

noncomputable def transitionPlan (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) : Plan (Γ := Γ) (Λ := Λ) (σ := σ) where
  «prefix» := (transitionPrefixKinds indexing).map fun kind => (sticky machineProgram kind, false)
  cells := (transitionCellKinds indexing).map (sticky machineProgram)
  carry := true

theorem transition_outputTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (input : Input) :
    outputTokens indexing (transitionPlan indexing machineProgram) input =
      TransitionTemplate.forestTokens indexing input.roots input.capacity machineProgram ++
        [.input (rootLookup input.roots (indexing.width input.capacity))] := by
  rw [outputTokens_eq_blocks]
  simp [transitionPlan, transitionPrefixKinds, transitionCellKinds,
    prefixTokens, listTokens, cellTokens, globalTokens, carriedTokens,
    TransitionTemplate.forestTokens, OutputOrder.outputOrder_eq_blocks,
    List.flatMap_append, List.flatMap_map, List.flatMap_assoc, withCursor, bitKind, bitCursor,
    List.append_assoc]

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan

open StatementCircuit TransitionTemplate AcceptanceTemplate
open PostfixModel VerifierCircuit TermMachine

local instance instFintypeΛTmBoolComputation_r3fb9fa_1 (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance instFintypeσTmBoolComputation_r3fb9fa_1 (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance instFintypeΓTmBoolComputation_r3fb9fa_1 (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan.instDecidableEqΛTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan.instDecidableEqσTmBoolComputation
attribute [local instance] OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan.instDecidableEqΓTmBoolComputation
def plan (V : NPVerifier) :
    TransitionMachine.Plan (Γ := V.computation.tm.Γ) (Λ := V.computation.tm.Λ)
      (σ := V.computation.tm.σ) where
  «prefix» :=
    ((List.finRange (indexing V).labelCount).map fun i =>
      (Global.label ((indexing V).labels.symm i),
        decide ((none : Option V.computation.tm.Λ) = (indexing V).labels.symm i))) ++
    ((List.finRange (indexing V).stateCount).map fun i =>
      (stateTemplate V ((indexing V).states.symm i), false))
  cells := (List.finRange (indexing V).symbolCount).map fun i =>
    let symbol := (indexing V).symbols.symm i
    cellTemplate V symbol.1 symbol.2
  carry := false

theorem label_tokens (V : NPVerifier) (roots : List Nat) (S cursor : Nat)
    (label : Option V.computation.tm.Λ) :
    (Global.label label).tokens (indexing V) roots S cursor ++
      (if decide ((none : Option V.computation.tm.Λ) = label) then [.not] else []) =
    mismatchTokens (configEncoding S (accepting V) (.inl label))
      (configWire (indexing V) roots S (.inl label)) := by
  rw [accepting_label]
  by_cases h : (none : Option V.computation.tm.Λ) = label
  · simp [Global.tokens, configWire, mismatchTokens, h]
  · simp [Global.tokens, configWire, mismatchTokens, h]

theorem state_tokens (V : NPVerifier) (roots : List Nat) (S cursor : Nat)
    (state : V.computation.tm.σ) :
    (stateTemplate V state).tokens (indexing V) roots S cursor =
      mismatchTokens (configEncoding S (accepting V) (.inr (.inl state)))
        (configWire (indexing V) roots S (.inr (.inl state))) := by
  rw [accepting_state]
  by_cases h : V.computation.tm.initialState = state
  · simp [stateTemplate, negateIf, Global.tokens, Term.tokens, configWire, mismatchTokens, h]
  · simp [stateTemplate, negateIf, Global.tokens, Term.tokens, configWire, mismatchTokens, h]

theorem cell_tokens (V : NPVerifier) (roots : List Nat) (S : Nat)
    (i : Fin S) (k : V.computation.tm.K) (symbol : Option (V.computation.tm.Γ k)) :
    (cellTemplate V k symbol).tokens (indexing V) roots S i.val =
      mismatchTokens (configEncoding S (accepting V) (.inr (.inr ⟨k, i, symbol⟩)))
        (configWire (indexing V) roots S (.inr (.inr ⟨k, i, symbol⟩))) := by
  rw [accepting_cell]
  have hS : 0 < S := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  by_cases hi : i.val = 0
  · cases hb : headMask V k symbol <;>
      simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        hS, hi, hb, mismatchTokens, configWire]
  · by_cases hs : (none : Option (V.computation.tm.Γ k)) = symbol
    · simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        i.isLt, hi, hs, mismatchTokens, configWire]
    · simp [cellTemplate, negateIf, Global.tokens, Term.tokens, Position.eval,
        i.isLt, hi, hs, mismatchTokens, configWire]

theorem outputTokens_eq (V : NPVerifier) (input : TermMachine.Input) :
    TransitionMachine.outputTokens (indexing V) (plan V) input =
      mismatchForest V input.roots input.capacity := by
  rw [TransitionMachine.outputTokens_eq_blocks]
  simp only [mismatchForest, OutputOrder.outputOrder_eq_blocks, List.flatMap_append,
    List.flatMap_map, List.flatMap_assoc]
  simp only [plan, TransitionMachine.prefixTokens, List.flatMap_append, List.flatMap_map,
    TransitionMachine.cellTokens, TransitionMachine.listTokens,
    TermMachine.globalTokens, TransitionMachine.withCursor_roots,
    TransitionMachine.withCursor_capacity, TransitionMachine.withCursor_cursor,
    TransitionMachine.carriedTokens, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  congr 1
  · congr 1
    · apply List.flatMap_congr
      intro i _
      exact label_tokens V input.roots input.capacity 0 ((indexing V).labels.symm i)
    · apply List.flatMap_congr
      intro i _
      simpa using state_tokens V input.roots input.capacity 0 ((indexing V).states.symm i)
  · apply List.flatMap_congr
    intro i _
    apply List.flatMap_congr
    intro j _
    exact cell_tokens V input.roots input.capacity i
      ((indexing V).symbols.symm j).1 ((indexing V).symbols.symm j).2

theorem fullTokens_eq (V : NPVerifier) (input : List Bool) (roots : List Nat) :
    AcceptanceTemplate.tokens V input (fun j => rootLookup roots j.val) =
      [.input (rootLookup roots (width V input))] ++
      TransitionMachine.outputTokens (indexing V) (plan V)
        ⟨0, capacity V input.length, roots⟩ ++
      InitializationTemplate.closeOr (width V input) ++ [.not, .and] := by
  rw [outputTokens_eq, mismatchForest_circuit]
  rfl

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptancePlan

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

open Turing MachineComposition StatementCircuit CircuitBatch TransitionTemplate

open TransitionArena

variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

noncomputable def tokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (snapshot : ProducerInvariant.Snapshot) : List PostfixModel.Token :=
  ProducerInvariant.transitionTokens indexing machineProgram S snapshot.roots

noncomputable def emitSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (snapshot : ProducerInvariant.Snapshot) : Nat :=
  TransitionMachine.steps indexing (TransitionMachine.transitionPlan indexing machineProgram)
    (termInput S snapshot)

theorem emitTraceAt {Caller : Type} (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ)
    (labels : TransitionMachine.Label indexing (TransitionMachine.transitionPlan indexing machineProgram) → Caller)
    (exit : Option Caller) (target : Caller → TM2.Stmt Alphabet Caller State)
    (code : ∀ label, target (labels label) = ForestPlacement.statement termPorts labels exit
      (TransitionMachine.program indexing (TransitionMachine.transitionPlan indexing machineProgram) label))
    (base : Tape → List Bool) (S remaining : Nat) (snapshot : ProducerInvariant.Snapshot)
    (valid : indexing.width S + 1 ≤ snapshot.roots.length) :
    (advance (TM2.step target))^[emitSteps indexing machineProgram S snapshot]
      (some ⟨some (labels (.prefix (TransitionMachine.compilePrefix indexing
        (TransitionMachine.transitionPlan indexing machineProgram).prefix).entry)),
        TermMachine.initialState, tapes base S remaining snapshot⟩) =
      some ⟨exit, TermMachine.initialState,
        preparedTapes base S remaining snapshot (tokens indexing machineProgram S snapshot)⟩ := by
  let input := termInput S snapshot
  let plan := TransitionMachine.transitionPlan indexing machineProgram
  have hv : TransitionMachine.Valid indexing plan input := by
    simpa [TransitionMachine.Valid, plan, TransitionMachine.transitionPlan, input, termInput] using valid
  have sourceTrace := TransitionMachine.fullTrace indexing plan input hv
    (fun tape => tapes base S remaining snapshot (termPorts tape))
    (termFrame base S remaining snapshot)
  have placed := ForestPlacement.trace termPorts labels exit (tapes base S remaining snapshot)
    (TransitionMachine.program indexing plan) target code
    (TransitionMachine.steps indexing plan input) _ _ sourceTrace
  simp only [ForestPlacement.configuration, ForestPlacement.placedLabel,
    ForestPlacement.fill_self] at placed
  rw [TransitionMachine.transition_outputTokens, place_emitTapes] at placed
  simpa only [emitSteps, tokens, ProducerInvariant.transitionTokens, input, termInput, plan]
    using placed

abbrev Label (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) :=
  Unit ⊕ (TransitionMachine.Label indexing
    (TransitionMachine.transitionPlan indexing machineProgram) ⊕ ForestStage.Label)

def entry (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) : Label indexing machineProgram := .inl ()

def emitLabel (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ)
    (label : TransitionMachine.Label indexing (TransitionMachine.transitionPlan indexing machineProgram)) :
    Label indexing machineProgram := .inr (.inl label)

def lowerLabel (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (label : ForestStage.Label) :
    Label indexing machineProgram := .inr (.inr label)

noncomputable def emitEntry (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) : Label indexing machineProgram :=
  emitLabel indexing machineProgram (.prefix (TransitionMachine.compilePrefix indexing
    (TransitionMachine.transitionPlan indexing machineProgram).prefix).entry)

def countdownStatement {Caller : Type} (next : Caller) : TM2.Stmt Alphabet Caller State :=
  .peek (.inr .countdown) (fun _ head => (((), head.getD false), none))
    (.branch (fun state => state.1.2)
      (.pop (.inr .countdown) (fun _ _ => TermMachine.initialState) (.goto fun _ => next))
      (.pop (.inr .countdown) (fun _ _ => TermMachine.initialState) .halt))

noncomputable def program (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) :
    Label indexing machineProgram → TM2.Stmt Alphabet (Label indexing machineProgram) State
  | .inl _ => countdownStatement (emitEntry indexing machineProgram)
  | .inr (.inl label) => ForestPlacement.statement termPorts (emitLabel indexing machineProgram)
      (some (lowerLabel indexing machineProgram .reverseTokens))
      (TransitionMachine.program indexing (TransitionMachine.transitionPlan indexing machineProgram) label)
  | .inr (.inr label) => ForestStage.statement (σ := Unit) forestPorts
      (lowerLabel indexing machineProgram) (some (entry indexing machineProgram)) label

noncomputable def machine (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) : FinTM2 where
  K := Tape
  k₀ := .inr .raw
  k₁ := .inl .records
  Γ := Alphabet
  Λ := Label indexing machineProgram
  main := entry indexing machineProgram
  σ := State
  initialState := TermMachine.initialState
  m := program indexing machineProgram

theorem guardZero (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S : Nat) (snapshot : ProducerInvariant.Snapshot) :
    (advance (TM2.step (program indexing machineProgram)))^[1]
      (some ⟨some (entry indexing machineProgram), TermMachine.initialState, tapes base S 0 snapshot⟩) =
      some ⟨none, TermMachine.initialState, finishTapes base S snapshot⟩ := by
  change some (TM2.stepAux (program indexing machineProgram (entry indexing machineProgram))
    TermMachine.initialState (tapes base S 0 snapshot)) = _
  simp [program, entry, countdownStatement, TM2.stepAux, tapes, encodeWord, finishTapes]

theorem guardSucc (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S remaining : Nat) (snapshot : ProducerInvariant.Snapshot) :
    (advance (TM2.step (program indexing machineProgram)))^[1]
      (some ⟨some (entry indexing machineProgram), TermMachine.initialState,
        tapes base S (remaining + 1) snapshot⟩) =
      some ⟨some (emitEntry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining snapshot⟩ := by
  change some (TM2.stepAux (program indexing machineProgram (entry indexing machineProgram))
    TermMachine.initialState (tapes base S (remaining + 1) snapshot)) = _
  simp only [program, entry, countdownStatement, TM2.stepAux]
  have hhead : (tapes base S (remaining + 1) snapshot (.inr .countdown)).head? = some true := by
    simp [tapes, encodeWord, List.replicate_succ]
  rw [hhead]
  simpa only [Option.getD_some, Bool.cond_true] using
    congrArg (fun stack => some (TM2.Cfg.mk (some (emitEntry indexing machineProgram))
      TermMachine.initialState stack)) (tapes_countdown_tail base S remaining snapshot)

variable {inputs : Nat}

noncomputable def stageGates (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : CircuitBatch.Frame inputs (indexing.width S + 1)) : List Gate :=
  Batch.gates (fun i => (frame.wires i).val) (ProducerInvariant.next frame)
    (List.ofFn (ProducerInvariant.stepExpressions indexing machineProgram S))

noncomputable def lowerSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : CircuitBatch.Frame inputs (indexing.width S + 1)) : Nat :=
  ForestStage.steps (tokens indexing machineProgram S (ProducerInvariant.snapshot frame))
    (ProducerInvariant.next frame)
    (ProducerInvariant.rootValues
      (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S))).reverse
    (stageGates indexing machineProgram S frame) (encodeWords (ProducerInvariant.rootValues frame))

noncomputable def stageSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : CircuitBatch.Frame inputs (indexing.width S + 1)) : Nat :=
  emitSteps indexing machineProgram S (ProducerInvariant.snapshot frame) +
    lowerSteps indexing machineProgram S frame

noncomputable def steps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat) :
    CircuitBatch.Frame inputs (indexing.width S + 1) → Nat → Nat
  | _, 0 => 1
  | frame, remaining + 1 => 1 + stageSteps indexing machineProgram S frame +
      steps indexing machineProgram S
        (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)) remaining

theorem place_forest_initial (base : Tape → List Bool) (S remaining : Nat)
    (snapshot : ProducerInvariant.Snapshot) (ts : List PostfixModel.Token) :
    ForestPlacement.fill forestPorts (tapes base S remaining snapshot)
      (ForestStage.initialLocal snapshot.current ts snapshot.reversedRecords
        (encodeWords snapshot.roots)) = preparedTapes base S remaining snapshot ts := by
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> simp [ForestStage.initialLocal, preparedTapes, tapes]
    | tokens => simp [ForestStage.initialLocal, preparedTapes]
    | records => simp [ForestStage.initialLocal, preparedTapes, tapes]
    | rootTable => simp [ForestStage.initialLocal, preparedTapes, tapes]
  | inr tape => cases tape <;> simp [preparedTapes, tapes]

theorem place_forest_final {oldWidth newWidth : Nat}
    (base : Tape → List Bool) (S remaining : Nat) (frame : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    ForestPlacement.fill forestPorts (tapes base S remaining (ProducerInvariant.snapshot frame))
      (ForestStage.finalLocal (ProducerInvariant.next (frame.step es))
        (ProducerInvariant.rootValues (frame.step es)).reverse
        (recordsBits (gateRecords
          (ProducerInvariant.next frame)
          (Batch.gates (fun i => (frame.wires i).val) (ProducerInvariant.next frame) (List.ofFn es))))
        (ProducerInvariant.snapshot frame).reversedRecords) =
      tapes base S remaining (ProducerInvariant.snapshot (frame.step es)) := by
  have hr := congrArg List.reverse (ProducerInvariant.recordBits_step frame es)
  rw [List.reverse_append] at hr
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> rfl
    | tokens => rfl
    | rootTable => simp only [ForestStage.finalLocal, List.reverse_reverse]; rfl
    | records => exact hr.symm
  | inr tape => cases tape <;> rfl

theorem stageTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S remaining : Nat) (frame : Frame inputs (indexing.width S + 1)) :
    (advance (TM2.step (program indexing machineProgram)))^[
        stageSteps indexing machineProgram S frame]
      (some ⟨some (emitEntry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining (ProducerInvariant.snapshot frame)⟩) =
      some ⟨some (entry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining (ProducerInvariant.snapshot
          (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)))⟩ := by
  let es := ProducerInvariant.stepExpressions indexing machineProgram S
  have emitted := emitTraceAt indexing machineProgram (emitLabel indexing machineProgram)
    (some (lowerLabel indexing machineProgram .reverseTokens)) (program indexing machineProgram)
    (fun _ => rfl) base S remaining (ProducerInvariant.snapshot frame)
    (by simp only [ProducerInvariant.snapshot, List.length_ofFn]; exact le_rfl)
  have compiled := ForestStage.traceAt (σ := Unit) forestPorts (lowerLabel indexing machineProgram)
    (some (entry indexing machineProgram)) (program indexing machineProgram) (fun _ => rfl)
    (tapes base S remaining (ProducerInvariant.snapshot frame)) ((), false)
    (tokens indexing machineProgram S (ProducerInvariant.snapshot frame))
    (ProducerInvariant.next frame) (ProducerInvariant.next (frame.step es))
    (ProducerInvariant.rootValues (frame.step es)).reverse (stageGates indexing machineProgram S frame)
    (ProducerInvariant.snapshot frame).reversedRecords (encodeWords (ProducerInvariant.rootValues frame))
    (ProducerInvariant.compile_transitionTokens indexing machineProgram S frame)
  have initial := place_forest_initial base S remaining (ProducerInvariant.snapshot frame)
    (tokens indexing machineProgram S (ProducerInvariant.snapshot frame))
  change ForestPlacement.fill forestPorts (tapes base S remaining (ProducerInvariant.snapshot frame))
      (ForestStage.initialLocal (ProducerInvariant.next frame)
        (tokens indexing machineProgram S (ProducerInvariant.snapshot frame))
        (ProducerInvariant.snapshot frame).reversedRecords (encodeWords (ProducerInvariant.rootValues frame))) = _ at initial
  rw [initial] at compiled
  have final := place_forest_final base S remaining frame es
  change ForestPlacement.fill forestPorts (tapes base S remaining (ProducerInvariant.snapshot frame))
      (ForestStage.finalLocal (ProducerInvariant.next (frame.step es))
        (ProducerInvariant.rootValues (frame.step es)).reverse
        (recordsBits (gateRecords (ProducerInvariant.next frame) (stageGates indexing machineProgram S frame)))
        (ProducerInvariant.snapshot frame).reversedRecords) = _ at final
  rw [final] at compiled
  simpa only [stageSteps, lowerSteps, emitEntry, es, TermMachine.initialState]
    using chain emitted compiled

theorem repeatTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (base : Tape → List Bool)
    (S : Nat) (frame : Frame inputs (indexing.width S + 1)) (remaining : Nat) :
    (advance (TM2.step (program indexing machineProgram)))^[steps indexing machineProgram S frame remaining]
      (some ⟨some (entry indexing machineProgram), TermMachine.initialState,
        tapes base S remaining (ProducerInvariant.snapshot frame)⟩) =
      some ⟨none, TermMachine.initialState, finishTapes base S (ProducerInvariant.snapshot
        (frame.repeat (ProducerInvariant.stepExpressions indexing machineProgram S) remaining))⟩ := by
  induction remaining generalizing frame with
  | zero => exact guardZero indexing machineProgram base S (ProducerInvariant.snapshot frame)
  | succ remaining ih =>
    have first := chain (guardSucc indexing machineProgram base S remaining (ProducerInvariant.snapshot frame))
      (stageTrace indexing machineProgram base S remaining frame)
    have result := chain first (ih (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)))
    simpa only [steps, ProducerInvariant.step_repeat] using result

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionIterationTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

open Turing MachineComposition TermMachine TransitionTemplate PostfixModel

def rootProgram (coefficient offset : Nat) : RootLabel → TM2.Stmt Alphabet RootLabel State
  | .seed => MachineUnaryAffineAt.seed .address offset .scan
  | .scan => MachineUnaryAffineAt.scan .capacity .scratch .address coefficient .scan .restore
  | .restore => Reduction.MachineTransfer.loopAt .scratch .capacity id false .restore
      (some (.lookup (.lookup (.run .copyFirst))))
  | .lookup label => MachineSubroutine.statement RootLabel.lookup none (lookupProgram 0 label)

section Indexed

variable {K Λ σ : Type} {Γ : K → Type}

def Valid (indexing : ConfigIndex.Indexing Γ Λ σ) (input : Input) : Prop :=
  indexing.width input.capacity < input.roots.length

theorem Valid.transition {indexing : ConfigIndex.Indexing Γ Λ σ} {input : Input}
    (valid : Valid indexing input) (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) :
    TransitionMachine.Valid indexing plan input := by
  unfold Valid at valid
  unfold TransitionMachine.Valid
  cases plan.carry <;> simp only [Bool.false_eq_true, ite_true, if_true, ite_false] <;> omega

theorem Valid.withCursor {indexing : ConfigIndex.Indexing Γ Λ σ} {input : Input}
    (valid : Valid indexing input) (cursor : Nat) :
    Valid indexing (TransitionMachine.withCursor input cursor) := valid

theorem widthAddress_eq (indexing : ConfigIndex.Indexing Γ Λ σ) (input : Input) :
    widthAddress indexing.symbolCount (indexing.labelCount + indexing.stateCount) input =
      indexing.width input.capacity := by
  simp [widthAddress, ConfigIndex.Indexing.width, Nat.mul_comm,
    Nat.add_comm, Nat.add_assoc]

def carryTokens (indexing : ConfigIndex.Indexing Γ Λ σ) (input : Input) : List Token :=
  [.input (rootLookup input.roots (indexing.width input.capacity))]

variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def finishEmitter (indexing : ConfigIndex.Indexing Γ Λ σ) :
    Emitter (Valid indexing) (fun _ => [.not, .and]) :=
  Emitter.literal (Valid indexing) [.not, .and]

end Indexed

open VerifierCircuit AcceptanceTemplate

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing MachineComposition StatementCircuit CircuitBatch
open PostfixModel PostfixAlignment ProducerInvariant VerifierCircuit
open TransitionArena

local instance iterationTimeVerifierLabelFintype_r3fb9fa_1 (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype_r3fb9fa_1 (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype_r3fb9fa_1 (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq_r3fb9fa_1 (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq_r3fb9fa_1 (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq_r3fb9fa_1 (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
theorem lower_final_eq {inputs oldWidth newWidth : Nat}
    (base : Tape → List Bool) (S : Nat) (frame : Frame inputs oldWidth)
    (es : Fin newWidth → Expr (Fin oldWidth)) :
    ForestPlacement.fill forestPorts (finishTapes base S (snapshot frame))
      (ForestStage.finalLocal (next (frame.step es)) (rootValues (frame.step es)).reverse
        (recordsBits (gateRecords (next frame)
          (Batch.gates (wireValues frame) (next frame) (List.ofFn es))))
        (recordBits frame).reverse) =
      finishTapes base S (snapshot (frame.step es)) := by
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;> rfl
    | tokens => rfl
    | records =>
      change (recordsBits (gateRecords (next frame)
        (Batch.gates (wireValues frame) (next frame) (List.ofFn es)))).reverse ++
        (recordBits frame).reverse = (recordBits (frame.step es)).reverse
      rw [recordBits_step, List.reverse_append]
      rfl
    | rootTable =>
      change encodeWords (rootValues (frame.step es)).reverse.reverse =
        encodeWords (rootValues (frame.step es))
      rw [List.reverse_reverse]
  | inr tape => cases tape <;> rfl

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_Completeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

open Turing MachineComposition StatementCircuit CircuitBatch PostfixModel PostfixAlignment

variable {K Λ σ : Type} [DecidableEq K]

structure FullPorts (K : Type) where
  emit : InitializationAssembly.Tape 9 ↪ K
  lower : ForestStage.Ports K
  output_shared : emit .reversed = lower .tokens
  count_shared : emit .count = lower (.lower .remaining)

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PackingAssignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PackingAssignments

open BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks

variable {Reg K : Type} [DecidableEq Reg] [DecidableEq K]

theorem constant_ready (destination : Reg) (constant : Nat) (values : Reg → Nat) :
    Ready (constantCommands destination constant) values := by
  simp [constantCommands, Ready, commandReady, result, BinaryRegisterProgram.destination,
    BinaryRegisterProgram.value]

theorem constant_result (destination : Reg) (constant : Nat) (values : Reg → Nat) :
    resultOf (constantCommands destination constant) values =
      Function.update values destination constant := by
  simp [constantCommands, resultOf_cons, result, BinaryRegisterProgram.destination,
    BinaryRegisterProgram.value]

end BinPackingGap.PackingAssignments

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Packing_PairExpressionCompiler
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeBEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGap.PairExpressionCompiler

open NatExpressionCompiler BinaryRegisterProgram

variable {α : Type} [DecidableEq α]

theorem num_correct (num den : Expr α) :
    Correct (input num den) (numNodes num den) (root num)
      (fun v => eval v num) (numCommands num den) :=
  compileInto_correct _ _ _ _

theorem den_correct (num den : Expr α) :
    Correct (input num den) (denNodes num den) (root den)
      (fun v => eval v den) (denCommands num den) :=
  compileInto_correct _ _ _ _

theorem first_preserves_input (num den : Expr α) (values : α → Nat) (a : α) :
    resultOf (numCommands num den) (initial num den values) (input num den a) = values a := by
  have h := num_correct num den (initial num den values) (fun _ => rfl)
  exact h.2.2 _ (by intros; simp [input, numNodes])

theorem first_den_empty (num den : Expr α) (values : α → Nat) (n : Node den) :
    resultOf (numCommands num den) (initial num den values) (denNodes num den n) = 0 := by
  have h := num_correct num den (initial num den values) (fun _ => rfl)
  exact h.2.2 _ (by
    intro node equal
    change (Sum.inr (Sum.inr n) : Reg num den) = Sum.inr (Sum.inl node) at equal
    cases Sum.inr.inj equal)

theorem ready (num den : Expr α) (values : α → Nat) :
    Ready (commands num den) (initial num den values) := by
  rw [commands, Ready_append]
  exact ⟨(num_correct num den (initial num den values) (fun _ => rfl)).1,
    (den_correct num den _ (first_den_empty num den values)).1⟩

theorem numerator_output (num den : Expr α) (values : α → Nat) :
    resultOf (commands num den) (initial num den values) (numRoot num den) = eval values num := by
  rw [commands, resultOf_append]
  have hn := num_correct num den (initial num den values) (fun _ => rfl)
  have hd := den_correct num den _ (first_den_empty num den values)
  rw [hd.2.2 (numRoot num den) (by
    intro node equal
    change (Sum.inr (Sum.inl (root num)) : Reg num den) = Sum.inr (Sum.inr node) at equal
    cases Sum.inr.inj equal)]
  simpa only [numRoot, initial, input] using hn.2.1

theorem denominator_output (num den : Expr α) (values : α → Nat) :
    resultOf (commands num den) (initial num den values) (denRoot num den) = eval values den := by
  rw [commands, resultOf_append]
  have hd := den_correct num den _ (first_den_empty num den values)
  simpa only [denRoot, first_preserves_input] using hd.2.1

theorem preserves_input (num den : Expr α) (values : α → Nat) (a : α) :
    resultOf (commands num den) (initial num den values) (input num den a) = values a := by
  rw [commands, resultOf_append]
  have hd := den_correct num den _ (first_den_empty num den values)
  rw [hd.2.2 (input num den a) (by intros; simp [input, denNodes])]
  exact first_preserves_input num den values a

theorem clearList_result {Reg : Type} [DecidableEq Reg]
    (registers : List Reg) (values : Reg → Nat) (r : Reg) :
    resultOf (clearList registers) values r = if r ∈ registers then 0 else values r := by
  induction registers generalizing values with
  | nil => simp [clearList]
  | cons s tail ih =>
    simp only [clearList, List.map_cons, resultOf_cons]
    rw [show tail.map Command.clear = clearList tail from rfl, ih]
    by_cases ht : r ∈ tail
    · simp [ht]
    · by_cases hs : r = s
      · subst r; simp [ht, result, destination, value]
      · simp [ht, hs, result, destination, value]

theorem clear_result (num den : Expr α) (values : Reg num den → Nat) :
    resultOf (clearCommands num den) values = initial num den (fun a => values (input num den a)) := by
  funext r
  rw [clearCommands, clearList_result]
  cases r with
  | inl a => simp [mem_temporaryList, initial, input]
  | inr n => simp [mem_temporaryList, initial]

theorem clear_after_consumed (num den : Expr α) (values : α → Nat) :
    resultOf (clearCommands num den)
      (consumed num den (resultOf (commands num den) (initial num den values))) =
        initial num den values := by
  rw [clear_result]
  congr 1
  funext a
  rw [consumed_input, preserves_input]

end BinPackingGap.PairExpressionCompiler

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

namespace BinPackingGap.PackingItemBlockMachine

open Turing BinPackingGames.Foundations.Complexity
open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler
open PairExpressionCompiler

variable {α K A : Type} [DecidableEq α] [DecidableEq K]

theorem exec (num den : Expr α) (slot : (Reg num den ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ i, slot i ≠ output) (base : K → List Bool)
    (values : α → Nat) (ambient : A) (width : Nat)
    (hwidth : ∀ a, (values a).size ≤ width) :
    ∃ steps ≤ (timePolynomial num den).eval width,
      Exec (code num den slot output)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base (initial num den values)⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          registerTapes slot (outputTapes output base (record num den values))
            (initial num den values)⟩ := by
  classical
  let start := initial num den values
  let computed := resultOf (commands num den) start
  let afterNum := Function.update computed (numRoot num den) 0
  let afterBoth := consumed num den computed
  let marked := Function.update base output (true :: base output)
  let writtenNum := Function.update marked output
    ((BinaryEncoding.natBits (computed (numRoot num den))).reverse ++ marked output)
  let writtenBoth := Function.update writtenNum output
    ((BinaryEncoding.natBits (afterNum (denRoot num den))).reverse ++ writtenNum output)
  let w := staticWidth (commands num den) width
  have hw0 : ∀ r, (start r).size ≤ width := initial_width num den values width hwidth
  have hw : ∀ r, (computed r).size ≤ w :=
    BinaryRegisterStructured.final_width (commands num den) start width hw0
  obtain ⟨calcSteps, calcBound, calcRun⟩ :=
    BinaryRegisterStructured.exec_polynomial slot (commands num den) base start
      (ready num den values) ambient width hw0
  have outside' : ¬ ∃ i, slot i = output := by rintro ⟨i, hi⟩; exact outside i hi
  have markerRun : Exec (.atom (.push output (fun _ => true) .done))
      ⟨BinaryAddMachine.clean ambient, registerTapes slot base computed⟩ 1
      ⟨BinaryAddMachine.clean ambient, registerTapes slot marked computed⟩ := by
    rw [RegisterFrameEmission.external_update slot base computed output outside]
    simpa only [Action.eval, registerTapes_other slot base computed output outside', marked] using
      Exec.atom (.push output (fun _ => true) .done)
        ⟨BinaryAddMachine.clean ambient, registerTapes slot base computed⟩
  have numRun := RegisterFrameEmission.exec slot marked computed
    (numRoot num den) output outside ambient
  have denRun := RegisterFrameEmission.exec slot writtenNum afterNum
    (denRoot num den) output outside ambient
  change Exec (RegisterFrameEmission.code (slot (.inl (numRoot num den))) output)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot marked computed⟩
    ((computed (numRoot num den)).size + 1)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot writtenNum afterNum⟩ at numRun
  change Exec (RegisterFrameEmission.code (slot (.inl (denRoot num den))) output)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot writtenNum afterNum⟩
    ((afterNum (denRoot num den)).size + 1)
    ⟨BinaryAddMachine.clean ambient, registerTapes slot writtenBoth afterBoth⟩ at denRun
  have hwc : ∀ r, (afterBoth r).size ≤ w := consumed_width num den computed w hw
  obtain ⟨clearSteps, clearBound, clearRun⟩ :=
    BinaryRegisterStructured.exec_polynomial slot (clearCommands num den) writtenBoth afterBoth
      (clear_ready num den afterBoth) ambient w hwc
  have denStill : afterNum (denRoot num den) = computed (denRoot num den) := by
    simp [afterNum, Ne.symm (numRoot_ne_denRoot num den)]
  have numValue : computed (numRoot num den) = eval values num := numerator_output num den values
  have denValue : computed (denRoot num den) = eval values den := denominator_output num den values
  have clearValue : resultOf (clearCommands num den) afterBoth = start :=
    clear_after_consumed num den values
  have writtenValue : writtenBoth = outputTapes output base (record num den values) := by
    simp only [writtenBoth, denStill, numValue, denValue, writtenNum, marked,
      Function.update_self, Function.update_idem, outputTapes, record,
      List.reverse_cons, List.reverse_append, List.append_assoc, List.singleton_append]
  let total := calcSteps + (1 + ((computed (numRoot num den)).size + 1 +
    ((afterNum (denRoot num den)).size + 1 + clearSteps)))
  refine ⟨total, ?_, ?_⟩
  · have hn := hw (numRoot num den)
    have hd := hw (denRoot num den)
    rw [timePolynomial_eval]
    change total ≤ (runtimePolynomial (commands num den)).eval width +
      (runtimePolynomial (clearCommands num den)).eval w + 2 * w + 5
    dsimp [total]
    rw [denStill]
    omega
  · rw [clearValue] at clearRun
    have combined := Exec.seq calcRun (Exec.seq markerRun
      (Exec.seq numRun (Exec.seq denRun clearRun)))
    rw [writtenValue] at combined
    exact combined

end BinPackingGap.PackingItemBlockMachine

namespace BinPackingGap.PackingChunkMachine

open FiniteTapeProgram BinaryRegisterProgram NatExpressionCompiler
open PairExpressionCompiler
open PackingItemBlockMachine (outputTapes)

variable {α δ K A : Type} [DecidableEq α] [DecidableEq K]

theorem exec_one (num den : Expr α) (slot : (Reg num den ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ i, slot i ≠ output) (base : K → List Bool)
    (values : α → Nat) (ambient : A) (width : Nat)
    (shape : registerTapes slot base (initial num den values) = base)
    (hwidth : ∀ a, (values a).size ≤ width) :
    ∃ steps ≤ (PackingItemBlockMachine.timePolynomial num den).eval width,
      Exec (PackingItemBlockMachine.code num den slot output)
        ⟨BinaryAddMachine.clean ambient, base⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          outputTapes output base (PackingItemBlockMachine.record num den values)⟩ := by
  obtain ⟨steps, bound, run⟩ :=
    PackingItemBlockMachine.exec num den slot output outside base values ambient width hwidth
  refine ⟨steps, bound, ?_⟩
  rw [shape, shape_after_output slot output outside base _ shape] at run
  exact run

theorem exec (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K)
    (output : K) (outside : ∀ d i, slot d i ≠ output)
    (descriptors : List δ) (base : K → List Bool) (values : δ → α → Nat)
    (ambient : A) (width : Nat)
    (shape : ∀ d ∈ descriptors,
      registerTapes (slot d) base (initial (numerator d) denominator (values d)) = base)
    (hwidth : ∀ d ∈ descriptors, ∀ a, (values d a).size ≤ width) :
    ∃ steps ≤ (timePolynomial numerator denominator descriptors).eval width,
      Exec (code numerator denominator slot output descriptors)
        ⟨BinaryAddMachine.clean ambient, base⟩ steps
        ⟨BinaryAddMachine.clean ambient,
          outputTapes output base (records numerator denominator values descriptors)⟩ := by
  induction descriptors generalizing base with
  | nil =>
      refine ⟨1, ?_, ?_⟩
      · simp [timePolynomial]
      · simpa only [code, records_nil, outputTapes_nil, Action.eval] using
          Exec.atom (.done : Action K (BinaryAddMachine.State A))
            ⟨BinaryAddMachine.clean ambient, base⟩
  | cons d rest ih =>
      have headShape := shape d (by simp)
      have headWidth := hwidth d (by simp)
      obtain ⟨headSteps, headBound, headRun⟩ :=
        exec_one (numerator d) denominator (slot d) output (outside d)
          base (values d) ambient width headShape headWidth
      cases rest with
      | nil =>
          refine ⟨headSteps, headBound, ?_⟩
          simpa only [code, records_cons, records_nil, List.append_nil] using headRun
      | cons e rest =>
          let middle := outputTapes output base
            (PackingItemBlockMachine.record (numerator d) denominator (values d))
          have tailShape : ∀ x ∈ e :: rest,
              registerTapes (slot x) middle
                (initial (numerator x) denominator (values x)) = middle := by
            intro x hx
            exact shape_after_output (slot x) output (outside x) base _
              (shape x (List.mem_cons.mpr (Or.inr hx))) _
          have tailWidth : ∀ x ∈ e :: rest, ∀ a, (values x a).size ≤ width := by
            intro x hx
            exact hwidth x (List.mem_cons.mpr (Or.inr hx))
          obtain ⟨tailSteps, tailBound, tailRun⟩ := ih middle tailShape tailWidth
          refine ⟨headSteps + tailSteps, ?_, ?_⟩
          · change headSteps + tailSteps ≤
              (PackingItemBlockMachine.timePolynomial (numerator d) denominator +
                timePolynomial numerator denominator (e :: rest)).eval width
            rw [Polynomial.eval_add]
            exact Nat.add_le_add headBound tailBound
          · have combined := Exec.seq headRun tailRun
            simpa only [code, middle, outputTapes_append, records_cons] using combined

end BinPackingGap.PackingChunkMachine

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Machines_GraphPackingJobList
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

def setupPolynomial : Polynomial Nat :=
  Polynomial.C (2 ^ (PackingSetupMachine.commands (parameters fixed K)).length) *
    (Polynomial.X + Polynomial.C (maxConstantSize (PackingSetupMachine.commands
      (parameters fixed K)) + 1))

end BinPackingGap.GraphPackingWidths

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

def inventory (x : GraphReductionInput) : InventoryData :=
  instantiate fixed x.graph (GraphPackingPreparation.repetitions fixed K x) x.k

end BinPackingGap.GraphPackingGlobalSemantics

namespace BinPackingGap.GraphPackingGlobalRuntime

open GraphPackingRegisters GraphPackingPreparation GraphPackingGlobalPhases
open GraphPackingPoolRuntime
open PackingItemExpression (denominator)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def adjustedWidthPolynomial : Polynomial Nat :=
  GraphPackingStockBounds.widthPolynomial fixed K + 1

def flagsPolynomial : Polynomial Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .edgePower 1).comp (adjustedWidthPolynomial fixed K) +
  poolListPolynomial fixed (flagPools fixed)
    (GraphPackingStockBounds.stockPolynomial fixed K) (adjustedWidthPolynomial fixed K) + 1

end BinPackingGap.GraphPackingGlobalRuntime

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_Initialization
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def loopStart (input : GenericGraphTables.Table q) :
    TM2.Cfg Alphabet (Driver.Label q) (State q) :=
  ⟨some .guard, initial q, loopTapes input⟩

theorem headerResult_eq (input : GenericGraphTables.Table q) :
    Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input) = loopTapes input := by
  funext tape
  cases tape <;> simp [Emitter.resultTapes, setupTapes, loopTapes]

theorem headerView_at (label : Emitter.Label (Driver.headerPlan q).length
    (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.header label) =
      Emitter.statement (Emitter.listCommands (Driver.headerPlan q)) headerSources
        Tape.scratch Tape.reversed Driver.Label.header (some .guard) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

def headerInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
      (some (loopStart input))
      (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) := by
  let view := MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
    (Driver.program q)
  have sourceScratch : ∀ i : Fin 2, headerSources i ≠ Tape.scratch := by
    intro i
    fin_cases i <;> decide
  have sourceOutput : ∀ i : Fin 2, headerSources i ≠ Tape.reversed := by
    intro i
    fin_cases i <;> decide
  have operands : ∀ i : Fin 2, setupTapes input (headerSources i) =
      encodeWord (![input.vertices, input.darts] i) := by
    intro i
    fin_cases i <;> rfl
  have run := EmitRows.headerInTime q input.vertices input.darts headerSources
    Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.header (some .guard) view headerView_at
    (setupTapes input) operands (by rfl) (initial q).1
    (GenericGraphTables.tableBits input).length
    (GenericGraphTables.vertices_le_tableBits_length input)
    (GenericGraphTables.darts_le_tableBits_length input)
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  change StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
    (some ⟨some .guard, initial q,
      Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input)⟩)
    (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) at transported
  rw [headerResult_eq] at transported
  exact transported

end BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPSourceHardness
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.PCP.AlphabetTable.LoopState

open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

theorem prefixWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixWords input (e + 1) =
      prefixWords input e ++ EmitRows.blockWords input ⟨e, he⟩ := by
  have bound : e < (List.finRange input.darts).length := by simpa using he
  have take := List.take_succ_eq_append_getElem bound
  have atIndex : (List.finRange input.darts)[e]'bound = (⟨e, he⟩ : Fin input.darts) := by
    simp
  rw [atIndex] at take
  unfold prefixWords
  rw [take, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem prefixBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    prefixBits input (e + 1) =
      prefixBits input e ++ encodeWords (EmitRows.blockWords input ⟨e, he⟩) := by
  rw [prefixBits, prefixWords_succ input e he, encodeWords_append]
  rfl

theorem prefixBits_reverse_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    (prefixBits input (e + 1)).reverse =
      (encodeWords (EmitRows.blockWords input ⟨e, he⟩)).reverse ++
        (prefixBits input e).reverse := by
  rw [prefixBits_succ input e he, List.reverse_append]

theorem prefixWords_full (input : GenericGraphTables.Table q) :
    prefixWords input input.darts = GraphTables.tableWords (Table.build input) := by
  have allRows : (List.finRange input.darts).take input.darts = List.finRange input.darts := by
    apply List.take_of_length_le
    simp
  unfold prefixWords
  rw [allRows]
  exact (EmitRows.tableWords_eq_blocks input).symm

theorem prefixBits_full (input : GenericGraphTables.Table q) :
    prefixBits input input.darts = GraphTables.tableBits (Table.build input) := by
  rw [prefixBits, prefixWords_full]
  rfl

theorem cursorWords_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorWords input e =
      GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)] ++
      cursorWords input (e + 1) := by
  have bound : e < (GenericGraphTables.rowList input).length := by
    simpa only [GenericGraphTables.rowList_length] using he
  unfold cursorWords
  rw [List.drop_eq_getElem_cons bound, List.flatMap_cons]
  simp only [GenericGraphTables.rowList, Vector.getElem_toList, Fin.getElem_fin]

theorem cursorBits_succ (input : GenericGraphTables.Table q) (e : Nat)
    (he : e < input.darts) :
    cursorBits input e =
      encodeWords (GenericGraphTables.rowWords input.rows[(⟨e, he⟩ : Fin input.darts)]) ++
      cursorBits input (e + 1) := by
  rw [cursorBits, cursorWords_succ input e he, encodeWords_append]
  rfl

end BinPackingGames.Foundations.PCP.AlphabetTable.LoopState

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Body

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def clearFieldsTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update base .tail []) .reverseIndex []) .head []

def clearFieldsInTime (base : Tape → List Bool) (ambient : Ambient q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (.clearField 0), (ambient, none), base⟩
      (some ⟨some .increment, (ambient, none), clearFieldsTapes base⟩)
      ((base .tail).length + (base .reverseIndex).length + (base .head).length + 3) := by
  let first := MachineDrain.drainInTime Tape.tail (Driver.Label.clearField 0)
    (some (.clearField 1)) (Driver.program q) (by rfl) base ambient none
  let second := MachineDrain.drainInTime Tape.reverseIndex (Driver.Label.clearField 1)
    (some (.clearField 2)) (Driver.program q) (by rfl)
    (Function.update base .tail []) ambient none
  let third := MachineDrain.drainInTime Tape.head (Driver.Label.clearField 2)
    (some .increment) (Driver.program q) (by rfl)
    (Function.update (Function.update base .tail []) .reverseIndex []) ambient none
  let firstTwo := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first second
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ firstTwo third
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have h := run.steps_le_m
  simp only [Function.update_of_ne (by decide : Tape.reverseIndex ≠ .tail),
    Function.update_of_ne (by decide : Tape.head ≠ .reverseIndex),
    Function.update_of_ne (by decide : Tape.head ≠ .tail)] at h
  omega

theorem emitterView_at (label :
    Emitter.Label (Driver.rowPlan q).length (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.emit label) =
      Emitter.statement (Emitter.listCommands (Driver.rowPlan q)) rowSources
        Tape.scratch Tape.reversed Driver.Label.emit (some (.clearField 0)) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

end BinPackingGames.Foundations.PCP.AlphabetTable.Body

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Loop

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

local instance prefixRunSizeOf (input : GenericGraphTables.Table q)
    (tapes : Tape → List Bool) (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    SizeOf (StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
      (prefixTime q (LoopState.inputBits input).length)) :=
  @StateTransition.EvalsToInTime._sizeOf_inst
    (TM2.Cfg Alphabet (Driver.Label q) (State q))
    (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length) inferInstance

end BinPackingGames.Foundations.PCP.AlphabetTable.Loop

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

noncomputable def time (q : Nat) : Polynomial Nat :=
  Finish.completedPolynomial q (prefixPolynomial q)

end BinPackingGames.Foundations.PCP.AlphabetTable.Runtime

namespace BinPackingGames.Foundations.PCP.RoundComputation

open Turing
open BinPackingGames.Foundations.Complexity

abbrev PoweringCertificate :=
  TM2ComputableInPolyTime
    (PortTables.inputBits (ports := PreprocessingTables.degree))
    (GenericGraphTables.tableBits (q := RoundTables.alphabet))
    (PoweringTables.transform PreprocessingTables.degree RoundTables.walkParameter)

noncomputable def poweredPolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits
      (GenericGraphTables.tableBits (q := RoundTables.alphabet))
      (RoundTables.powered H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits _
    (fun table => PoweringTables.transform PreprocessingTables.degree
      RoundTables.walkParameter (PreprocessingTables.output H table))
  exact MachineSequential.composeBits preprocessing powering

end BinPackingGames.Foundations.PCP.RoundComputation

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_Search_SearchUpdateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGap.SearchUpdateMachine

open Turing BinPackingGames.Foundations.Complexity MachineComposition
open BinPackingGames.Reduction.MachineTransfer
open SearchSemantics SearchEncoding BinaryEncoding

def newFixed (s : State) := s.fixed.set s.item (some s.label)

end BinPackingGap.SearchUpdateMachine

end OAI
end


