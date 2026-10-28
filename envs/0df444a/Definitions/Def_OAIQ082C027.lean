-- Prove2me | Definitions.Def_OAIQ082C027
-- name    : OAIQ082C027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:09:33.099928+00:00
-- url     : https://prove2.me/theorems/d2176209-471c-45c2-bf2d-11e78f662f27
-- title:
--   Definitions bundle OAIQ082C027 of the split of OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.BinPackingGap.main_results`, carved from OpenAI's openai/math development (OpenAI, *Additive hardness and unbounded configuration gaps in bin packing (result family 118)*, OpenAI Math Release, September 24, 2026, result family 118, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 255 declarations of OpenAI's Lean: 132 definitions, 6 inductive types or structures, 1 instance and 116 theorems. The definitions and types are `OAI.BinPackingCompleteness.PCPSourceHardness.computation`, `OAI.BinPackingCompleteness.PCPSourceMachine.normalizedComputation`, `OAI.BinPackingCompleteness.PreprocessingMachine.computableInPolyTime`, `OAI.BinPackingCompleteness.PreprocessingMachine.round`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.carryEmitter`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.closureEmitter`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.orEmitter`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.outputTokens`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.program`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.rootEmitter`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.steps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.timeConstant`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.timePolynomial`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine.verifierInput`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.EmitLabel`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.emissionSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.entry`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.expressions`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.loweringSteps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.machine`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.prepared`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.program`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.steps`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.verifierInPolynomialTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage.verifierPlacedInPolynomialTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.verifierFinalTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.verifierInPolynomialTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.verifierInitialTapes`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish.verifierPlacedInPolynomialTime`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.Completeness.verifierReduction`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.Agrees`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.FullReady`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.Label`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.Prepared`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.Ready`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.emitLabels`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.entry`, `OAI.BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage.finishedLocal` and 98 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: [`BinPacking_Computation_PoweringMachineRuntime`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Computation/PoweringMachineRuntime.lean), [`BinPacking_CookLevin_Completeness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/CookLevin/Completeness.lean), [`BinPacking_CookLevin_ProducerFrontStage`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/CookLevin/ProducerFrontStage.lean), [`BinPacking_CookLevin_TransitionIterationTime`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/CookLevin/TransitionIterationTime.lean), [`BinPacking_Inventory_PackingConstantPool`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/PackingConstantPool.lean), [`BinPacking_Machines_GraphPackingGlobalExecution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingGlobalExecution.lean), [`BinPacking_Machines_GraphPackingJobList`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/GraphPackingJobList.lean), [`BinPacking_Machines_PackingVertexUpdate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Machines/PackingVertexUpdate.lean), [`BinPacking_PCP_Initialization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/PCP/Initialization.lean), [`BinPacking_PCP_PCPSourceHardness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/PCP/PCPSourceHardness.lean), [`BinPacking_Packing_PackingAssignments`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/PackingAssignments.lean), [`BinPacking_Search_SearchUpdateMachine`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Search/SearchUpdateMachine.lean).
--
--   **Imports.** It imports the published bundle `Def_BinPackingGap`; the bundles `OAIQ082C023`, `OAIQ082C024` and `OAIQ082C025` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ082C029`.
-- source:
--   OpenAI, Additive hardness and unbounded configuration gaps in bin packing (result family 118), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 118; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Std
import Definitions.Def_BinPackingGap
import Definitions.Def_OAIQ082C023
import Definitions.Def_OAIQ082C024
import Definitions.Def_OAIQ082C025

section
-- module Solutions.OAIQ082_BP.BinPacking_Computation_PoweringMachineRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BinPackingGames.Foundations.Complexity.PoweringGlobalConfiguration

open Turing PoweringMachineGlobal

@[simp] theorem boolList_mpr_eq (h : List Bool = List Bool) (bits : List Bool) :
    h.mpr bits = bits := rfl

end BinPackingGames.Foundations.Complexity.PoweringGlobalConfiguration

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

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

open Turing

theorem bootstrapPrepared_other (V : NPVerifier) (input : List Bool) (t : Tape V)
    (hc : t ≠ current V) (ht : t ≠ count V) (hz : t ≠ cursor V) :
    bootstrapPrepared V input t = frontendPrepared V input t :=
  ProducerBootstrap.prepared_other (bootstrapPorts V) (frontendPrepared V input) t hc ht hz

def initializationBase (V : NPVerifier) (input : List Bool) :
    InitializationAssembly.Tape 9 → List Bool
  | .rawInput => input
  | .framedInput => encodeWord input.length ++ input
  | .witnessBound => encodeWord (V.witnessBound.eval input.length)
  | .capacity => encodeWord (VerifierCircuit.capacity V input.length)
  | .count => encodeWord 0
  | _ => []

theorem bootstrap_initialization_view (V : NPVerifier) (input : List Bool) :
    (fun t => bootstrapPrepared V input (initializationPorts V t)) =
      initializationBase V input := by
  funext t
  cases t <;>
    simp [initializationTape, initializationBase, bootstrapPrepared,
      ProducerBootstrap.prepared, ProducerBootstrap.copied,
      frontendPrepared, frontTapes, current, count, cursor, tokens, shared,
      raw, framed, q, capacity, freeInputs, clock,
      VerifierFront.prepared_raw, VerifierFront.prepared_stream, VerifierFront.prepared_clock,
      ClockPreparation.clockValue, encodeWord]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerArena

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerFrontStage

open Turing ProducerArena

abbrev Label (V : NPVerifier) := VerifierFront.Label V ⊕ ProducerBootstrap.Label

def entry (V : NPVerifier) : Label V := .inl (.inl 0)

def statement {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ) :
    Label V → TM2.Stmt (Alphabet V) Λ State
  | .inl l => ForestPlacement.statement (frontPorts V) (fun l => labels (.inl l))
      (some (labels (.inr .copy))) (VerifierFront.program (A := Unit × Bool) V l)
  | .inr l => ProducerBootstrap.statement (bootstrapPorts V) (fun l => labels (.inr l)) exit l

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  VerifierFront.timePolynomial V +
    Polynomial.C 2 * WitnessEncoding.freeInputPolynomial V.witnessBound + Polynomial.C 5

theorem timePolynomial_eval (V : NPVerifier) (n : Nat) :
    (timePolynomial V).eval n = (VerifierFront.timePolynomial V).eval n +
      (2 * (2 * V.witnessBound.eval n + 1) + 5) := by
  simp [timePolynomial, Nat.add_assoc]

def inTime {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet V) Λ State)
    (code : ∀ l, program (labels l) = statement V labels exit l)
    (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initialTapes V input⟩
      (some ⟨exit, initialState, bootstrapPrepared V input⟩)
      ((timePolynomial V).eval input.length) := by
  have front := ForestPlacement.execution (frontPorts V)
    (fun l => labels (.inl l)) (some (labels (.inr .copy))) (empty V)
    (VerifierFront.program (A := Unit × Bool) V) program (fun l => code (.inl l))
    (VerifierFront.prepareInTime V input ((), false))
  have front' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initialTapes V input⟩
      (some ⟨some (labels (.inr .copy)), initialState, frontendPrepared V input⟩)
      ((VerifierFront.timePolynomial V).eval input.length) := by
    simpa only [ForestPlacement.configuration, ForestPlacement.placedLabel,
      front_fill, entry, initialTapes, frontendPrepared, initialState,
      TermMachine.initialState] using front
  have boot := ProducerBootstrap.inTime (bootstrapPorts V) (fun l => labels (.inr l))
    exit program (fun l => code (.inr l)) (frontendPrepared V input)
    (2 * V.witnessBound.eval input.length + 1) (bootstrapReady V input) ((), false) none
  have combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ front' boot
  simpa only [timePolynomial_eval, bootstrapPrepared, initialState,
    TermMachine.initialState, Nat.add_comm] using combined

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerFrontStage

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_TransitionIterationTime
attribute [-instance] _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

open Turing MachineComposition TermMachine TransitionTemplate PostfixModel

theorem rootTrace (coefficient offset : Nat) (input : Input)
    (present : input.roots[widthAddress coefficient offset input]? =
      some (rootLookup input.roots (widthAddress coefficient offset input)))
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (rootProgram coefficient offset)))^[rootSteps coefficient offset input]
      (some ⟨some .seed, initialState, base⟩) =
      some ⟨none, initialState, emitTapes base
        [.input (rootLookup input.roots (widthAddress coefficient offset input))]⟩ := by
  have ha := frame.clean .address (by rfl)
  have hs := frame.clean .scratch (by rfl)
  have affine := MachineUnaryAffineAt.seededAffineTrace .capacity .scratch .address
    (by decide) (by decide) (by decide) coefficient offset RootLabel.seed
    RootLabel.scan RootLabel.restore (some (.lookup (.lookup (.run .copyFirst))))
    (rootProgram coefficient offset) rfl rfl rfl base input.capacity []
    (by simpa using frame.capacityWord) hs ((), false) none
  simp only [ha, List.append_nil] at affine
  have source := lookupTailTrace 0 input (widthAddress coefficient offset input) present base frame
  have lookup := MachineSubroutine.trace RootLabel.lookup none (lookupProgram 0)
    (rootProgram coefficient offset) (fun _ => rfl)
    (MachinePreservingLookupClean.steps input.roots (widthAddress coefficient offset input) +
      rootLookup input.roots (widthAddress coefficient offset input) + 4) _ _ source
  simp only [MachineSubroutine.configuration, MachineSubroutine.label] at lookup
  exact trace_trans _ affine lookup

theorem rootSteps_le (coefficient offset : Nat) (input : Input)
    (present : input.roots[widthAddress coefficient offset input]? =
      some (rootLookup input.roots (widthAddress coefficient offset input))) :
    rootSteps coefficient offset input ≤ 12 * (input.size + 1) := by
  have hl := MachinePreservingLookupClean.steps_le input.roots
    (widthAddress coefficient offset input) _ present
  have hw := MachineLookupSpec.output_length_le input.roots
    (widthAddress coefficient offset input) _ present
  rw [encodeWord_length] at hw
  unfold rootSteps Input.size
  omega

def rootEmitter (valid : Input → Prop) (coefficient offset : Nat)
    (present : ∀ input, valid input →
      input.roots[widthAddress coefficient offset input]? =
        some (rootLookup input.roots (widthAddress coefficient offset input))) :
    Emitter valid (fun input =>
      [.input (rootLookup input.roots (widthAddress coefficient offset input))]) where
  Label := RootLabel
  finite := inferInstance
  entry := .seed
  program := rootProgram coefficient offset
  steps := rootSteps coefficient offset
  constant := 12
  trace input hv base frame := rootTrace coefficient offset input (present input hv) base frame
  bound input hv := rootSteps_le coefficient offset input (present input hv)

theorem closureTrace (coefficient offset : Nat) (input : Input)
    (base : Tape → List Bool) (frame : Frame input base) :
    (advance (TM2.step (closureProgram coefficient offset)))^[closureSteps coefficient offset input]
      (some ⟨some .seed, initialState, base⟩) =
      some ⟨none, initialState, emitTapes base
        (InitializationTemplate.closeOr (widthAddress coefficient offset input))⟩ := by
  let width := widthAddress coefficient offset input
  let finished := OrClosure.frame closurePorts base (encodeWord 0)
    ((tokenBits (InitializationTemplate.closeOr width)).reverse ++ base .reversed)
    (List.replicate (width + 1) true ++ base .count)
  have hp := frame.clean .position (by rfl)
  have hs := frame.clean .scratch (by rfl)
  have affine := MachineUnaryAffineAt.seededAffineTrace .capacity .scratch .position
    (by decide) (by decide) (by decide) coefficient offset ClosureLabel.seed
    ClosureLabel.scan ClosureLabel.restore (some .orSeed)
    (closureProgram coefficient offset) rfl rfl rfl base input.capacity []
    (by simpa using frame.capacityWord) hs ((), false) none
  simp only [hp, List.append_nil] at affine
  have closure := OrClosure.closureTrace closurePorts ClosureLabel.orSeed ClosureLabel.orLoop
    (some .finish) (closureProgram coefficient offset) rfl rfl base width []
    (base .reversed) (base .count) ((), false) none
  have startFrame : OrClosure.frame closurePorts base (encodeWord width ++ [])
      (base .reversed) (base .count) = Function.update base .position (encodeWord width) := by
    funext tape
    cases tape <;> simp [OrClosure.frame, closurePorts]
  rw [startFrame] at closure
  simp only [List.append_nil] at closure
  have finish : (advance (TM2.step (closureProgram coefficient offset)))^[1]
      (some ⟨some .finish, initialState, finished⟩) =
      some ⟨none, initialState, emitTapes base (InitializationTemplate.closeOr width)⟩ := by
    change some (TM2.stepAux (closureProgram coefficient offset .finish) initialState finished) = _
    simp only [closureProgram, TM2.stepAux]
    congr 2
    funext tape
    cases tape <;> simp [finished, OrClosure.frame, closurePorts, emitTapes,
      InitializationTemplate.closeOr, encodeWord, hp, Nat.add_comm]
  exact trace_trans _ (trace_trans _ affine closure) finish

def closureEmitter (valid : Input → Prop) (coefficient offset : Nat) :
    Emitter valid (fun input => InitializationTemplate.closeOr (widthAddress coefficient offset input)) where
  Label := ClosureLabel
  finite := inferInstance
  entry := .seed
  program := closureProgram coefficient offset
  steps := closureSteps coefficient offset
  constant := coefficient + offset + 8
  trace input _ base frame := closureTrace coefficient offset input base frame
  bound input _ := closureSteps_le coefficient offset input

section Indexed

variable {K Λ σ : Type} {Γ : K → Type}

variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]

def carryEmitter (indexing : ConfigIndex.Indexing Γ Λ σ) :
    Emitter (Valid indexing) (carryTokens indexing) :=
  (rootEmitter (Valid indexing) indexing.symbolCount (indexing.labelCount + indexing.stateCount)
    (fun input hv => by
      rw [widthAddress_eq]
      simp only [rootLookup, List.getElem?_eq_getElem hv, Option.getD_some])).congr
        (fun input => by rw [widthAddress_eq]; rfl)

def orEmitter (indexing : ConfigIndex.Indexing Γ Λ σ) :
    Emitter (Valid indexing) (fun input => InitializationTemplate.closeOr (indexing.width input.capacity)) :=
  (closureEmitter (Valid indexing) indexing.symbolCount (indexing.labelCount + indexing.stateCount)).congr
    (fun input => by rw [widthAddress_eq])

inductive Label (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ))
  | carry (label : (carryEmitter indexing).Label)
  | mismatch (label : TransitionMachine.Label indexing plan)
  | close (label : (orEmitter indexing).Label)
  | finish (label : (finishEmitter indexing).Label)
  deriving Fintype

attribute [-instance] instFintypeLabel

instance labelFintype (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Fintype (Label indexing plan) :=
  Fintype.ofEquiv
    ((carryEmitter indexing).Label ⊕ TransitionMachine.Label indexing plan ⊕
      (orEmitter indexing).Label ⊕ (finishEmitter indexing).Label)
    (Label.proxyTypeEquiv indexing plan)

def program (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) :
    Label indexing plan → TM2.Stmt Alphabet (Label indexing plan) State
  | .carry label => MachineSubroutine.statement Label.carry
      (some (.mismatch (.prefix (TransitionMachine.compilePrefix indexing plan.prefix).entry)))
      ((carryEmitter indexing).program label)
  | .mismatch label => MachineSubroutine.statement Label.mismatch
      (some (.close (orEmitter indexing).entry)) (TransitionMachine.program indexing plan label)
  | .close label => MachineSubroutine.statement Label.close
      (some (.finish (finishEmitter indexing).entry)) ((orEmitter indexing).program label)
  | .finish label => MachineSubroutine.statement Label.finish none ((finishEmitter indexing).program label)

def outputTokens (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : List Token :=
  carryTokens indexing input ++ TransitionMachine.outputTokens indexing plan input ++
    InitializationTemplate.closeOr (indexing.width input.capacity) ++ [.not, .and]

def steps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input) : Nat :=
  (carryEmitter indexing).steps (TransitionMachine.withCursor input 0) +
    TransitionMachine.steps indexing plan input +
    (orEmitter indexing).steps (TransitionMachine.withCursor input 0) + 1

omit [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [(tape : K) → DecidableEq (Γ tape)] [(tape : K) → Fintype (Γ tape)]
  [DecidableEq Λ] [Fintype Λ] in
theorem fullTrace (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing input) (base : Tape → List Bool)
    (frame : Frame (TransitionMachine.withCursor input 0) base) :
    (advance (TM2.step (program indexing plan)))^[steps indexing plan input]
      (some ⟨some (Label.carry (carryEmitter indexing).entry), initialState, base⟩) =
      some ⟨none, initialState, emitTapes base (outputTokens indexing plan input)⟩ := by
  let carried := emitTapes base (carryTokens indexing input)
  let mismatch := emitTapes carried (TransitionMachine.outputTokens indexing plan input)
  let closed := emitTapes mismatch (InitializationTemplate.closeOr (indexing.width input.capacity))
  have carry := (carryEmitter indexing).traceAt Label.carry
    (some (.mismatch (.prefix (TransitionMachine.compilePrefix indexing plan.prefix).entry)))
    (program indexing plan) (fun _ => rfl) (TransitionMachine.withCursor input 0)
    (valid.withCursor 0) base frame
  have hcarry : Frame (TransitionMachine.withCursor input 0) carried :=
    frame.emit (carryTokens indexing input)
  have mid := TransitionMachine.traceAt indexing plan Label.mismatch
    (some (.close (orEmitter indexing).entry)) (program indexing plan) (fun _ => rfl)
    input (valid.transition plan) carried hcarry
  have hmid := hcarry.emit (TransitionMachine.outputTokens indexing plan input)
  have close := (orEmitter indexing).traceAt Label.close
    (some (.finish (finishEmitter indexing).entry)) (program indexing plan) (fun _ => rfl)
    (TransitionMachine.withCursor input 0) (valid.withCursor 0) mismatch hmid
  have hclose := hmid.emit (InitializationTemplate.closeOr (indexing.width input.capacity))
  have finish := (finishEmitter indexing).traceAt Label.finish none
    (program indexing plan) (fun _ => rfl) (TransitionMachine.withCursor input 0)
    (valid.withCursor 0) closed hclose
  have h := trace_trans _ (trace_trans _ (trace_trans _ carry mid) close) finish
  simpa only [steps, carried, mismatch, closed, finishEmitter, Emitter.literal,
    TransitionMachine.withCursor_capacity, TransitionMachine.withCursor_roots,
    carryTokens, emitTapes_append, outputTokens, List.append_assoc] using h

def timeConstant (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Nat :=
  (carryEmitter indexing).constant + TransitionMachine.timeConstant indexing plan +
    (orEmitter indexing).constant + 1

noncomputable def timePolynomial (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) : Polynomial Nat :=
  Polynomial.C (timeConstant indexing plan) * (Polynomial.X + 1)^2

omit [DecidableEq K] [Fintype σ] [DecidableEq σ]
  [(tape : K) → DecidableEq (Γ tape)] [(tape : K) → Fintype (Γ tape)]
  [DecidableEq Λ] [Fintype Λ] in
theorem steps_le (indexing : ConfigIndex.Indexing Γ Λ σ)
    (plan : TransitionMachine.Plan (Γ := Γ) (Λ := Λ) (σ := σ)) (input : Input)
    (valid : Valid indexing input) :
    steps indexing plan input ≤ timeConstant indexing plan * (TransitionMachine.dataSize input + 1)^2 := by
  have hc := (carryEmitter indexing).bound (TransitionMachine.withCursor input 0) (valid.withCursor 0)
  have hm := TransitionMachine.steps_le indexing plan input (valid.transition plan)
  have ho := (orEmitter indexing).bound (TransitionMachine.withCursor input 0) (valid.withCursor 0)
  have hs : (TransitionMachine.withCursor input 0).size = TransitionMachine.dataSize input := by
    simp [TransitionMachine.withCursor, Input.size, TransitionMachine.dataSize]
  rw [hs] at hc ho
  have hsq : TransitionMachine.dataSize input + 1 ≤ (TransitionMachine.dataSize input + 1)^2 := by
    nlinarith
  have hc' := hc.trans (Nat.mul_le_mul_left (carryEmitter indexing).constant hsq)
  have ho' := ho.trans (Nat.mul_le_mul_left (orEmitter indexing).constant hsq)
  unfold steps timeConstant
  nlinarith

end Indexed

open VerifierCircuit AcceptanceTemplate

local instance iterationTimeVerifierLabelFintype_r258638_1 (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype_r258638_1 (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype_r258638_1 (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq_r258638_1 (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq_r258638_1 (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq_r258638_1 (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
def verifierInput (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) : Input :=
  ⟨0, capacity V input.length, List.ofFn wire⟩

theorem verifierInput_valid (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    Valid (indexing V) (verifierInput V input wire) := by
  simp [Valid, verifierInput, width]

theorem outputTokens_eq_acceptance (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    outputTokens (indexing V) (AcceptancePlan.plan V) (verifierInput V input wire) =
      AcceptanceTemplate.tokens V input wire := by
  have hw : (fun j : Fin (width V input + 1) => rootLookup (List.ofFn wire) j.val) = wire :=
    funext (rootLookup_ofFn wire)
  have h := (AcceptancePlan.fullTokens_eq V input (List.ofFn wire)).symm
  rw [hw] at h
  simpa only [outputTokens, carryTokens, verifierInput, width] using h

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing MachineComposition StatementCircuit CircuitBatch
open PostfixModel PostfixAlignment ProducerInvariant VerifierCircuit
open TransitionArena

local instance iterationTimeVerifierLabelFintype_r258638_2 (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype_r258638_2 (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype_r258638_2 (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq_r258638_2 (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq_r258638_2 (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq_r258638_2 (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
abbrev EmitLabel (V : NPVerifier) :=
  AcceptanceMachine.Label (indexing V) (AcceptancePlan.plan V)

abbrev Label (V : NPVerifier) := EmitLabel V ⊕ ForestStage.Label

def entry (V : NPVerifier) : Label V :=
  .inl (.carry (AcceptanceMachine.carryEmitter (indexing V)).entry)

def program (V : NPVerifier) : Label V → TM2.Stmt Alphabet (Label V) State
  | .inl label => ForestPlacement.statement termPorts Sum.inl
      (some (.inr .reverseTokens))
      (AcceptanceMachine.program (indexing V) (AcceptancePlan.plan V) label)
  | .inr label => ForestStage.statement forestPorts Sum.inr none label

def machine (V : NPVerifier) : FinTM2 where
  K := Tape
  k₀ := .inr .capacity
  k₁ := .inl .records
  Γ := Alphabet
  Λ := Label V
  main := entry V
  σ := State
  initialState := TermMachine.initialState
  m := program V

def expressions (V : NPVerifier) (input : List Bool) :
    Fin 1 → Expr (Fin (width V input + 1)) :=
  fun _ => acceptanceExpr V input

theorem tokens_eq_forest (V : NPVerifier) (input : List Bool)
    (wire : Fin (width V input + 1) → Nat) :
    AcceptanceTemplate.tokens V input wire =
      forestTokens wire (List.ofFn (expressions V input)) := by
  rw [AcceptanceTemplate.tokens_eq]
  simp [expressions, List.ofFn_succ, forestTokens]

theorem finish_termFrame (base : Tape → List Bool) (S : Nat) (s : Snapshot) :
    TermMachine.Frame (termInput S s)
      (fun tape => finishTapes base S s (termPorts tape)) := by
  have restriction : (fun tape => finishTapes base S s (termPorts tape)) =
      (fun tape => tapes base S 0 s (termPorts tape)) := by
    simp only [termPorts]
    funext tape
    change Function.update (tapes base S 0 s) (Sum.inr Extra.countdown) [] (termTape tape) =
      tapes base S 0 s (termTape tape)
    cases tape <;> simp [termTape]
  rw [restriction]
  exact termFrame base S 0 s

def prepared (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) : Tape → List Bool :=
  Function.update
    (Function.update (finishTapes base S s) (.inl .tokens) (tokenBits tokens).reverse)
    (.inl (.lower .remaining)) (encodeWord tokens.length)

theorem finish_place_emitTapes (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) :
    ForestPlacement.fill termPorts (finishTapes base S s)
      (TermMachine.emitTapes (fun tape => finishTapes base S s (termPorts tape)) tokens) =
      prepared base S s tokens := by
  simp only [TermMachine.emitTapes, ForestPlacement.fill_update, ForestPlacement.fill_self]
  simp [termTape, tapes, finishTapes, prepared, encodeWord]

theorem prepared_eq_lower (base : Tape → List Bool) (S : Nat) (s : Snapshot)
    (tokens : List Token) :
    prepared base S s tokens =
      ForestPlacement.fill forestPorts (finishTapes base S s)
        (ForestStage.initialLocal s.current tokens s.reversedRecords (encodeWords s.roots)) := by
  rw [fill_forest]
  funext tape
  cases tape with
  | inl tape =>
    cases tape with
    | lower tape => cases tape <;>
        simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
    | tokens => simp [prepared, finishTapes, ForestStage.initialLocal]
    | records => simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
    | rootTable => simp [prepared, finishTapes, tapes, ForestStage.initialLocal]
  | inr tape => cases tape <;>
      simp [prepared, finishTapes, tapes]

def emissionSteps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  AcceptanceMachine.steps (indexing V) (AcceptancePlan.plan V)
    (AcceptanceMachine.verifierInput V input (wireValues frame))

def loweringSteps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  ForestStage.steps (AcceptanceTemplate.tokens V input (wireValues frame)) (next frame)
    (rootValues (frame.step (expressions V input))).reverse
    (Batch.gates (wireValues frame) (next frame) (List.ofFn (expressions V input)))
    (encodeWords (rootValues frame))

def steps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) : Nat :=
  emissionSteps V input frame + loweringSteps V input frame

theorem fullTrace (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) (base : Tape → List Bool) :
    (advance (TM2.step (program V)))^[steps V input frame]
      (some ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot frame)⟩) =
      some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (frame.step (expressions V input)))⟩ := by
  let boundary := finishTapes base (capacity V input.length) (snapshot frame)
  let wire := wireValues frame
  let inp := AcceptanceMachine.verifierInput V input wire
  let tokens := AcceptanceTemplate.tokens V input wire
  have hframe : TermMachine.Frame inp (fun tape => boundary (termPorts tape)) :=
    finish_termFrame base (capacity V input.length) (snapshot frame)
  have source := AcceptanceMachine.fullTrace (indexing V) (AcceptancePlan.plan V) inp
    (AcceptanceMachine.verifierInput_valid V input wire)
    (fun tape => boundary (termPorts tape)) hframe
  rw [AcceptanceMachine.outputTokens_eq_acceptance] at source
  have emitter := ForestPlacement.trace termPorts Sum.inl (some (.inr .reverseTokens))
    boundary (AcceptanceMachine.program (indexing V) (AcceptancePlan.plan V))
    (program V) (fun _ => rfl) _ _ _ source
  change (advance (TM2.step (program V)))^[emissionSteps V input frame]
    (some ⟨some (entry V), TermMachine.initialState,
      ForestPlacement.fill termPorts boundary (fun tape => boundary (termPorts tape))⟩) =
      some ⟨some (.inr .reverseTokens), TermMachine.initialState,
        ForestPlacement.fill termPorts boundary
          (TermMachine.emitTapes (fun tape => boundary (termPorts tape)) tokens)⟩ at emitter
  rw [ForestPlacement.fill_self] at emitter
  rw [finish_place_emitTapes, prepared_eq_lower] at emitter
  have valid := compile_frameForest frame (expressions V input)
  rw [← tokens_eq_forest] at valid
  have lower := ForestStage.traceAt forestPorts Sum.inr none (program V) (fun _ => rfl)
    boundary ((), false) tokens (next frame) (next (frame.step (expressions V input)))
    (rootValues (frame.step (expressions V input))).reverse
    (Batch.gates wire (next frame) (List.ofFn (expressions V input)))
    (recordBits frame).reverse (encodeWords (rootValues frame)) valid
  rw [lower_final_eq] at lower
  exact chain _ emitter lower

theorem verifierTrace (V : NPVerifier) (input : List Bool) (base : Tape → List Bool) :
    (advance (TM2.step (program V)))^[
      steps V input (timeFrame V input (V.horizon input.length))]
      (some ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (timeFrame V input (V.horizon input.length)))⟩) =
      some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot (finalFrame V input))⟩ :=
  fullTrace V input (timeFrame V input (V.horizon input.length)) base

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerTime

open CircuitBatch StatementCircuit PostfixModel PostfixAlignment ProducerInvariant
open MachineComposition VerifierCircuit
open scoped BigOperators

local instance iterationTimeVerifierLabelFintype (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def loweringPolynomial (V : NPVerifier) : Polynomial Nat :=
  ForestStage.timePolynomial.comp (4 * stageEnvelopePolynomial V + 1)

def transitionEmissionPolynomial (V : NPVerifier) : Polynomial Nat :=
  (TransitionMachine.timePolynomial (indexing V)
    (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)).comp
      (2 * stageEnvelopePolynomial V)

def acceptanceEmissionPolynomial (V : NPVerifier) : Polynomial Nat :=
  (AcceptanceMachine.timePolynomial (indexing V) (AcceptancePlan.plan V)).comp
    (2 * stageEnvelopePolynomial V)

def finishPolynomial (V : NPVerifier) : Polynomial Nat :=
  9 * budgetPolynomial V + tapePolynomial V + 18

def iterationPolynomial (V : NPVerifier) : Polynomial Nat :=
  Bounds.horizonPolynomial V.computation.time V.witnessBound *
    (1 + transitionEmissionPolynomial V + loweringPolynomial V) + 1

variable {inputs oldWidth newWidth : Nat}

theorem forestSteps_le (V : NPVerifier) (input : List Bool)
    (f : Frame inputs oldWidth) (es : Fin newWidth → Expr (Fin oldWidth))
    (oldRoots : List Bool)
    (hc : next f ≤ (stageEnvelopePolynomial V).eval input.length)
    (he : Batch.cost (List.ofFn es) ≤ (stageEnvelopePolynomial V).eval input.length)
    (ht : (tokenBits (forestTokens (fun i => (f.wires i).val) (List.ofFn es))).length ≤
      (stageEnvelopePolynomial V).eval input.length)
    (hr : oldRoots.length ≤ (stageEnvelopePolynomial V).eval input.length) :
    forestSteps f es oldRoots ≤ (loweringPolynomial V).eval input.length := by
  have h := ForestStage.forest_steps_le (fun i => (f.wires i).val)
    (List.ofFn es) (next f) oldRoots (fun i => (f.wires i).isLt)
  change ForestStage.steps _ _ _ _ _ ≤ _
  apply h.trans
  rw [loweringPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  omega

def transitionForestSteps (V : NPVerifier) (input : List Bool) (t : Nat) : Nat :=
  forestSteps (timeFrame V input t) (VerifierCircuit.stepExpressions V input)
    (snapshot (timeFrame V input t)).rootBits

theorem transitionForestSteps_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t < V.horizon input.length) :
    transitionForestSteps V input t ≤ (loweringPolynomial V).eval input.length := by
  obtain ⟨_, hc, he, hr, htok⟩ := timeFrame_stageEnvelope V input t ht
  exact forestSteps_le V input _ _ _ hc he htok hr

def acceptanceForestSteps (V : NPVerifier) (input : List Bool) : Nat :=
  forestSteps (timeFrame V input (V.horizon input.length))
    (fun _ : Fin 1 => acceptanceExpr V input)
    (snapshot (timeFrame V input (V.horizon input.length))).rootBits

theorem acceptanceForestSteps_le (V : NPVerifier) (input : List Bool) :
    acceptanceForestSteps V input ≤ (loweringPolynomial V).eval input.length := by
  have hg := circuitOfVerifier_gates_le_polynomial V input
  rw [circuitOfVerifier_gate_count] at hg
  have hb := budgetPolynomial_eval V input
  have hE := stageEnvelopePolynomial_eval V input
  have hc := timeFrame_current_le V input (V.horizon input.length) le_rfl
  have hr := (timeFrame_lengths_le V input (V.horizon input.length) le_rfl).2.1
  have htok := acceptance_tokens_length_le V input
  apply forestSteps_le
  · omega
  · simp only [List.ofFn_succ, List.ofFn_zero, Batch.cost_cons, Batch.cost_nil, Nat.add_zero]
    omega
  · exact htok.trans (by omega)
  · exact hr.trans (by omega)

def frameInput (V : NPVerifier) (input : List Bool) (t : Nat) : TermMachine.Input :=
  AcceptanceMachine.verifierInput V input (fun i => ((timeFrame V input t).wires i).val)

theorem frameInput_dataSize_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    TransitionMachine.dataSize (frameInput V input t) ≤
      2 * (stageEnvelopePolynomial V).eval input.length := by
  have hE := stageEnvelopePolynomial_eval V input
  have hr := (timeFrame_lengths_le V input t ht).2.1
  change capacity V input.length + (snapshot (timeFrame V input t)).rootBits.length ≤ _
  omega

def transitionEmissionSteps (V : NPVerifier) (input : List Bool) (t : Nat) : Nat :=
  TransitionMachine.steps (indexing V) (TransitionMachine.transitionPlan (indexing V)
    V.computation.tm.m) (frameInput V input t)

theorem transitionEmissionSteps_le (V : NPVerifier) (input : List Bool) (t : Nat)
    (ht : t ≤ V.horizon input.length) :
    transitionEmissionSteps V input t ≤ (transitionEmissionPolynomial V).eval input.length := by
  have hv : TransitionMachine.Valid (indexing V)
      (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)
      (frameInput V input t) := by
    simp [TransitionMachine.Valid, TransitionMachine.transitionPlan, frameInput,
      AcceptanceMachine.verifierInput, width]
  have h := TransitionMachine.steps_le (indexing V)
    (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m) (frameInput V input t) hv
  change TransitionMachine.steps _ _ _ ≤ _
  have he : TransitionMachine.timeConstant (indexing V)
      (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m) *
      (TransitionMachine.dataSize (frameInput V input t) + 1)^2 =
      (TransitionMachine.timePolynomial (indexing V)
        (TransitionMachine.transitionPlan (indexing V) V.computation.tm.m)).eval
          (TransitionMachine.dataSize (frameInput V input t)) := by
    simp [TransitionMachine.timePolynomial]
  rw [he] at h
  apply h.trans
  rw [transitionEmissionPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simpa using frameInput_dataSize_le V input t ht

def acceptanceEmissionSteps (V : NPVerifier) (input : List Bool) : Nat :=
  AcceptanceMachine.steps (indexing V) (AcceptancePlan.plan V)
    (frameInput V input (V.horizon input.length))

theorem acceptanceEmissionSteps_le (V : NPVerifier) (input : List Bool) :
    acceptanceEmissionSteps V input ≤ (acceptanceEmissionPolynomial V).eval input.length := by
  have hv := AcceptanceMachine.verifierInput_valid V input
    (fun i => ((timeFrame V input (V.horizon input.length)).wires i).val)
  have h := AcceptanceMachine.steps_le (indexing V) (AcceptancePlan.plan V)
    (frameInput V input (V.horizon input.length)) hv
  change AcceptanceMachine.steps _ _ _ ≤ _
  have he : AcceptanceMachine.timeConstant (indexing V) (AcceptancePlan.plan V) *
      (TransitionMachine.dataSize (frameInput V input (V.horizon input.length)) + 1)^2 =
      (AcceptanceMachine.timePolynomial (indexing V) (AcceptancePlan.plan V)).eval
        (TransitionMachine.dataSize (frameInput V input (V.horizon input.length))) := by
    simp [AcceptanceMachine.timePolynomial]
  rw [he] at h
  apply h.trans
  rw [acceptanceEmissionPolynomial, Polynomial.eval_comp]
  apply natPolynomial_eval_mono
  simpa using frameInput_dataSize_le V input (V.horizon input.length) le_rfl

def finishSteps (V : NPVerifier) (input : List Bool) : Nat :=
  let C := circuitOfVerifier V input
  CircuitFinish.totalTime C.wires C.inputs C.output.val (recordsBits C.records).length

theorem finishSteps_le (V : NPVerifier) (input : List Bool) :
    finishSteps V input ≤ (finishPolynomial V).eval input.length := by
  let C := circuitOfVerifier V input
  have hf : C.inputs ≤ C.wires := Nat.le_add_right _ _
  have h := CircuitFinish.totalTime_le C.wires C.inputs C.output.val
    (recordsBits C.records).length hf C.output.isLt
  have hg := circuitOfVerifier_gates_le_polynomial V input
  have hb := budgetPolynomial_eval V input
  have hr := (finalFrame_lengths_le V input).2.2
  have hr' : (recordsBits C.records).length ≤ (tapePolynomial V).eval input.length := by
    simpa only [snapshot, List.length_reverse, Circuit.records, finalFrame, C,
      circuitOfVerifier, Frame.toCircuit, Fragment.toCircuit] using hr
  have hc : C.wires ≤ (budgetPolynomial V).eval input.length := by
    change (2 * V.witnessBound.eval input.length + 1) +
      (circuitOfVerifier V input).gates.length ≤ _
    omega
  unfold finishSteps
  apply h.trans
  simp only [finishPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat]
  omega

theorem iterationPolynomial_eval (V : NPVerifier) (input : List Bool) :
    (iterationPolynomial V).eval input.length = V.horizon input.length *
      (1 + (transitionEmissionPolynomial V).eval input.length +
        (loweringPolynomial V).eval input.length) + 1 := by
  simp [iterationPolynomial, NPVerifier.horizon]

def iterationSteps (V : NPVerifier) (input : List Bool) : Nat :=
  (∑ t ∈ Finset.range (V.horizon input.length),
    (1 + transitionEmissionSteps V input t + transitionForestSteps V input t)) + 1

theorem iterationSteps_le (V : NPVerifier) (input : List Bool) :
    iterationSteps V input ≤ (iterationPolynomial V).eval input.length := by
  rw [iterationPolynomial_eval]
  unfold iterationSteps
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _t ∈ Finset.range (V.horizon input.length),
        (1 + (transitionEmissionPolynomial V).eval input.length +
          (loweringPolynomial V).eval input.length) := by
      apply Finset.sum_le_sum
      intro t ht
      have hlt := Finset.mem_range.mp ht
      exact Nat.add_le_add
        (Nat.add_le_add_left (transitionEmissionSteps_le V input t (Nat.le_of_lt hlt)) 1)
        (transitionForestSteps_le V input t hlt)
    _ = _ := by simp

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerTime

namespace BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

open Turing MachineComposition StatementCircuit CircuitBatch TransitionArena
open scoped BigOperators

section Generic
variable {K Λ σ : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype σ] [DecidableEq σ]
variable [∀ k, DecidableEq (Γ k)] [∀ k, Fintype (Γ k)] [DecidableEq Λ] [Fintype Λ]
variable {inputs : Nat}

theorem steps_eq_sum (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) (remaining : Nat) :
    steps indexing machineProgram S frame remaining =
      (∑ t ∈ Finset.range remaining,
        (1 + stageSteps indexing machineProgram S
          (frame.repeat (ProducerInvariant.stepExpressions indexing machineProgram S) t))) + 1 := by
  induction remaining generalizing frame with
  | zero => simp [steps]
  | succ remaining ih =>
    rw [steps, ih, Finset.sum_range_succ']
    simp only [ProducerInvariant.step_repeat, Frame.repeat]
    omega

theorem tokens_frame_eq_forest (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) :
    tokens indexing machineProgram S (ProducerInvariant.snapshot frame) =
      PostfixAlignment.forestTokens (fun i => (frame.wires i).val)
        (List.ofFn (ProducerInvariant.stepExpressions indexing machineProgram S)) := by
  rw [tokens, ProducerInvariant.transitionTokens_eq]
  have hw : (fun i : Fin (indexing.width S + 1) =>
      (ProducerInvariant.snapshot frame).roots[i.val]?.getD 0) =
      (fun i => (frame.wires i).val) := by
    funext i
    change (List.ofFn (fun i => (frame.wires i).val))[i.val]?.getD 0 = _
    rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]
    rfl
  rw [hw]

theorem lowerSteps_eq_forestSteps (indexing : ConfigIndex.Indexing Γ Λ σ)
    (machineProgram : Λ → TM2.Stmt Γ Λ σ) (S : Nat)
    (frame : Frame inputs (indexing.width S + 1)) :
    lowerSteps indexing machineProgram S frame =
      ProducerTime.forestSteps frame (ProducerInvariant.stepExpressions indexing machineProgram S)
        (encodeWords (ProducerInvariant.rootValues frame)) := by
  unfold lowerSteps ProducerTime.forestSteps
  rw [tokens_frame_eq_forest]
  have roots := ProducerInvariant.step_roots frame (ProducerInvariant.stepExpressions indexing machineProgram S)
  change ProducerInvariant.rootValues (frame.step (ProducerInvariant.stepExpressions indexing machineProgram S)) = _ at roots
  rw [roots]
  rfl

end Generic

local instance iterationTimeVerifierLabelFintype (V : NPVerifier) : Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance iterationTimeVerifierStateFintype (V : NPVerifier) : Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance iterationTimeVerifierAlphabetFintype (V : NPVerifier) : ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance iterationTimeVerifierLabelDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance iterationTimeVerifierStateDecidableEq (V : NPVerifier) : DecidableEq V.computation.tm.σ := Classical.decEq _
local instance iterationTimeVerifierAlphabetDecidableEq (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

theorem stageSteps_verifier (V : NPVerifier) (input : List Bool) (t : Nat) :
    stageSteps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.timeFrame V input t) =
      ProducerTime.transitionEmissionSteps V input t + ProducerTime.transitionForestSteps V input t := by
  rw [stageSteps, lowerSteps_eq_forestSteps, ProducerInvariant.stepExpressions_verifier]
  rfl

theorem verifier_steps_eq (V : NPVerifier) (input : List Bool) :
    steps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input)
      (V.horizon input.length) = ProducerTime.iterationSteps V input := by
  rw [steps_eq_sum, ProducerInvariant.stepExpressions_verifier]
  unfold ProducerTime.iterationSteps
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  change 1 + stageSteps (VerifierCircuit.indexing V) V.computation.tm.m
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.timeFrame V input t) = _
  rw [stageSteps_verifier]
  omega

theorem verifier_steps_le (V : NPVerifier) (input : List Bool) :
    steps (VerifierCircuit.indexing V) V.computation.tm.m
      (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input)
      (V.horizon input.length) ≤ (ProducerTime.iterationPolynomial V).eval input.length := by
  rw [verifier_steps_eq]
  exact ProducerTime.iterationSteps_le V input

noncomputable def verifierInPolynomialTime (V : NPVerifier) (input : List Bool)
    (base : Tape → List Bool) :
    StateTransition.EvalsToInTime
      (machine (VerifierCircuit.indexing V) V.computation.tm.m).step
      ⟨some (entry (VerifierCircuit.indexing V) V.computation.tm.m), TermMachine.initialState,
        tapes base (VerifierCircuit.capacity V input.length) (V.horizon input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.initialFrame V input))⟩
      (some ⟨none, TermMachine.initialState,
        finishTapes base (VerifierCircuit.capacity V input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length)))⟩)
      ((ProducerTime.iterationPolynomial V).eval input.length) where
  steps := steps (VerifierCircuit.indexing V) V.computation.tm.m
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input) (V.horizon input.length)
  evals_in_steps := repeatTrace (VerifierCircuit.indexing V) V.computation.tm.m base
    (VerifierCircuit.capacity V input.length) (VerifierCircuit.initialFrame V input) (V.horizon input.length)
  steps_le_m := verifier_steps_le V input

noncomputable def verifierPlacedInPolynomialTime {CallerTape CallerLabel : Type}
    [DecidableEq CallerTape] (V : NPVerifier) (input : List Bool)
    (ports : Tape ↪ CallerTape)
    (labels : Label (VerifierCircuit.indexing V) V.computation.tm.m → CallerLabel)
    (exit : Option CallerLabel)
    (target : CallerLabel → TM2.Stmt (fun _ : CallerTape => Bool) CallerLabel State)
    (code : ∀ label, target (labels label) = ForestPlacement.statement ports labels exit
      (program (VerifierCircuit.indexing V) V.computation.tm.m label))
    (ambient : CallerTape → List Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (entry (VerifierCircuit.indexing V) V.computation.tm.m)), TermMachine.initialState,
        ForestPlacement.fill ports ambient
          (tapes base (VerifierCircuit.capacity V input.length) (V.horizon input.length)
            (ProducerInvariant.snapshot (VerifierCircuit.initialFrame V input)))⟩
      (some ⟨exit, TermMachine.initialState,
        ForestPlacement.fill ports ambient (finishTapes base (VerifierCircuit.capacity V input.length)
          (ProducerInvariant.snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length))))⟩)
      ((ProducerTime.iterationPolynomial V).eval input.length) := by
  simpa only [ForestPlacement.configuration, ForestPlacement.placedLabel] using
    ForestPlacement.execution ports labels exit ambient
      (program (VerifierCircuit.indexing V) V.computation.tm.m) target code
      (verifierInPolynomialTime V input base)

end BinPackingGames.Foundations.Complexity.CookLevin.TransitionIteration

end

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_CookLevin_Completeness
attribute [-instance] _root_.OAI.BinPackingCompleteness.PCPSource.clauseCount_neZero _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.BinPackingGames.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.BinPackingGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instFintypeLocalTape _root_.OAI.BinPackingGap.FiniteTapeProgram.Code.labelFintype _root_.OAI.BinPackingGap.LiteralSlotGraph.instDecidableConflict _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.Packing.instFintypeTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq _root_.OAI.BinPackingGap.UniformTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

open Turing MachineComposition StatementCircuit CircuitBatch TransitionArena
open ProducerInvariant VerifierCircuit

local instance completenessLabelFintype_r258638_1 (V : NPVerifier) :
    Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance completenessStateFintype_r258638_1 (V : NPVerifier) :
    Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance completenessAlphabetFintype_r258638_1 (V : NPVerifier) :
    ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance completenessLabelDecidableEq_r258638_1 (V : NPVerifier) :
    DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance completenessStateDecidableEq_r258638_1 (V : NPVerifier) :
    DecidableEq V.computation.tm.σ := Classical.decEq _
local instance completenessAlphabetDecidableEq_r258638_1 (V : NPVerifier) :
    ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
theorem loweringSteps_eq_forestSteps (V : NPVerifier) (input : List Bool) {inputs : Nat}
    (frame : Frame inputs (width V input + 1)) :
    loweringSteps V input frame =
      ProducerTime.forestSteps frame (expressions V input) (encodeWords (rootValues frame)) := by
  unfold loweringSteps ProducerTime.forestSteps
  rw [tokens_eq_forest]
  have roots := step_roots frame (expressions V input)
  change rootValues (frame.step (expressions V input)) =
    Batch.roots (next frame) (List.ofFn (expressions V input)) at roots
  rw [roots]
  rfl

theorem verifier_steps_eq (V : NPVerifier) (input : List Bool) :
    steps V input (timeFrame V input (V.horizon input.length)) =
      ProducerTime.acceptanceEmissionSteps V input +
        ProducerTime.acceptanceForestSteps V input := by
  rw [steps, loweringSteps_eq_forestSteps]
  rfl

theorem verifier_steps_le (V : NPVerifier) (input : List Bool) :
    steps V input (timeFrame V input (V.horizon input.length)) ≤
      (ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V).eval
        input.length := by
  rw [verifier_steps_eq, Polynomial.eval_add]
  exact Nat.add_le_add (ProducerTime.acceptanceEmissionSteps_le V input)
    (ProducerTime.acceptanceForestSteps_le V input)

def verifierInPolynomialTime (V : NPVerifier) (input : List Bool)
    (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine V).step
      ⟨some (entry V), TermMachine.initialState,
        finishTapes base (capacity V input.length)
          (snapshot (timeFrame V input (V.horizon input.length)))⟩
      (some ⟨none, TermMachine.initialState,
        finishTapes base (capacity V input.length) (snapshot (finalFrame V input))⟩)
      ((ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V).eval
        input.length) where
  steps := steps V input (timeFrame V input (V.horizon input.length))
  evals_in_steps := verifierTrace V input base
  steps_le_m := verifier_steps_le V input

def verifierPlacedInPolynomialTime {CallerTape CallerLabel : Type}
    [DecidableEq CallerTape] (V : NPVerifier) (input : List Bool)
    (ports : Tape ↪ CallerTape) (labels : Label V → CallerLabel) (exit : Option CallerLabel)
    (target : CallerLabel → TM2.Stmt (fun _ : CallerTape => Bool) CallerLabel State)
    (code : ∀ label, target (labels label) =
      ForestPlacement.statement ports labels exit (program V label))
    (ambient : CallerTape → List Bool) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels (entry V)), TermMachine.initialState,
        ForestPlacement.fill ports ambient
          (finishTapes base (capacity V input.length)
            (snapshot (timeFrame V input (V.horizon input.length))))⟩
      (some ⟨exit, TermMachine.initialState,
        ForestPlacement.fill ports ambient
          (finishTapes base (capacity V input.length) (snapshot (finalFrame V input)))⟩)
      ((ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V).eval
        input.length) := by
  simpa only [ForestPlacement.configuration, ForestPlacement.placedLabel] using
    ForestPlacement.execution ports labels exit ambient (program V) target code
      (verifierInPolynomialTime V input base)

end BinPackingGames.Foundations.Complexity.CookLevin.AcceptanceStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

open Turing

variable {σ : Type}

def verifierInitialTapes (V : NPVerifier) (input : List Bool) : Tape → List Bool :=
  let C := VerifierCircuit.circuitOfVerifier V input
  initialTapes C.wires C.inputs C.output.val (recordsBits C.records)

def verifierFinalTapes (V : NPVerifier) (input : List Bool) : Tape → List Bool :=
  memory [] [] [] [] (circuitBits (VerifierCircuit.circuitOfVerifier V input)) [] []

def verifierInPolynomialTime (V : NPVerifier) (input : List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .copyOut, (ambient, register), verifierInitialTapes V input⟩
      (some ⟨none, (ambient, none), verifierFinalTapes V input⟩)
      ((ProducerTime.finishPolynomial V).eval input.length) := by
  let run := circuitInTime (VerifierCircuit.circuitOfVerifier V input) ambient register
  exact {
    steps := run.steps
    evals_in_steps := run.evals_in_steps
    steps_le_m := ProducerTime.finishSteps_le V input }

def verifierPlacedInPolynomialTime {K Λ : Type} [DecidableEq K]
    (ports : Tape ↪ K) (labels : Label → Λ) (exit : Option Λ)
    (base : K → List Bool)
    (target : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, target (labels l) = ForestPlacement.statement ports labels exit (program l))
    (V : NPVerifier) (input : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .copyOut), (ambient, register),
        ForestPlacement.fill ports base (verifierInitialTapes V input)⟩
      (some ⟨exit, (ambient, none), ForestPlacement.fill ports base (verifierFinalTapes V input)⟩)
      ((ProducerTime.finishPolynomial V).eval input.length) :=
  ForestPlacement.execution ports labels exit base program target code
    (verifierInPolynomialTime V input ambient register)

theorem verifierFinal_output (V : NPVerifier) (input : List Bool) :
    verifierFinalTapes V input .output =
      circuitBits (VerifierCircuit.circuitOfVerifier V input) := rfl

end BinPackingGames.Foundations.Complexity.CookLevin.CircuitFinish

namespace BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

open Turing MachineComposition StatementCircuit CircuitBatch PostfixModel PostfixAlignment

def freeInputs (V : NPVerifier) (input : List Bool) : Nat :=
  2 * V.witnessBound.eval input.length + 1

def initialGates (V : NPVerifier) (input : List Bool) : List Gate :=
  Batch.gates Fin.val (freeInputs V input)
    (List.ofFn (VerifierCircuit.initialExpressions V input))

def preparedLocal (V : NPVerifier) (input : List Bool) : ForestStage.Tape → List Bool :=
  ForestStage.initialLocal (freeInputs V input)
    (InitializationTemplate.initializationTokens V input) [] []

def snapshotLocal (s : ProducerInvariant.Snapshot) : ForestStage.Tape → List Bool
  | .lower .current => s.currentBits
  | .lower .remaining => encodeWord 0
  | .records => s.reversedRecords
  | .rootTable => s.rootBits
  | _ => []

def finishedLocal (V : NPVerifier) (input : List Bool) : ForestStage.Tape → List Bool :=
  snapshotLocal (ProducerInvariant.snapshot (VerifierCircuit.initialFrame V input))

theorem initialCompile (V : NPVerifier) (input : List Bool) :
    compileTokens (freeInputs V input) []
      (InitializationTemplate.initializationTokens V input) =
      some (ProducerInvariant.next (VerifierCircuit.initialFrame V input),
        (ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input)).reverse,
        initialGates V input) := by
  have h := ProducerInvariant.compile_frameForest
    (Frame.initial (id : Fin (freeInputs V input) → Fin (freeInputs V input)))
    (VerifierCircuit.initialExpressions V input)
  simpa [InitializationTemplate.initializationTokens_eq, freeInputs, initialGates,
    ProducerInvariant.next, Frame.initial, Fragment.empty,
    VerifierCircuit.initialFrame] using h

theorem initialRecords (V : NPVerifier) (input : List Bool) :
    ProducerInvariant.recordBits (VerifierCircuit.initialFrame V input) =
      recordsBits (gateRecords (freeInputs V input) (initialGates V input)) := by
  change ProducerInvariant.recordBits
    ((Frame.initial (id : Fin (freeInputs V input) → Fin (freeInputs V input))).step
      (VerifierCircuit.initialExpressions V input)) = _
  erw [ProducerInvariant.recordBits_step]
  simp [ProducerInvariant.recordBits, ProducerInvariant.next, Frame.initial,
    Fragment.empty, gateRecords, recordsBits, recordsWords, encodeWords,
    freeInputs, initialGates]

theorem finalLocal_eq (V : NPVerifier) (input : List Bool) :
    ForestStage.finalLocal
      (ProducerInvariant.next (VerifierCircuit.initialFrame V input))
      (ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input)).reverse
      (recordsBits (gateRecords (freeInputs V input) (initialGates V input))) [] =
      finishedLocal V input := by
  rw [← initialRecords]
  funext tape
  cases tape with
  | lower tape => cases tape <;>
      simp [ForestStage.finalLocal, finishedLocal, snapshotLocal,
        ProducerInvariant.next, ProducerInvariant.snapshot,
        ProducerInvariant.Snapshot.currentBits]
  | tokens => rfl
  | records => simp [ForestStage.finalLocal, finishedLocal, snapshotLocal,
      ProducerInvariant.snapshot, ProducerInvariant.recordBits]
  | rootTable => simp [ForestStage.finalLocal, finishedLocal, snapshotLocal,
      ProducerInvariant.snapshot, ProducerInvariant.rootValues,
      ProducerInvariant.Snapshot.rootBits]

def lowerSteps (V : NPVerifier) (input : List Bool) : Nat :=
  ForestStage.steps (InitializationTemplate.initializationTokens V input)
    (freeInputs V input)
    (ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input)).reverse
    (initialGates V input) []

variable {K Λ σ : Type} [DecidableEq K]

def Ready (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) : Prop :=
  ∀ t, base (p t) = ForestStage.initialLocal (freeInputs V input) [] [] [] t

def Prepared (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) : Prop :=
  ∀ t, base (p t) = preparedLocal V input t

def result (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) : K → List Bool :=
  ForestPlacement.fill p base (finishedLocal V input)

theorem prepared_emitted (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) (ready : Ready p base V input) :
    Prepared p
      (ClashMachine.emitted (p .tokens) (p (.lower .remaining)) base
        (InitializationTemplate.initializationTokens V input)) V input := by
  dsimp only [Ready] at ready
  intro t
  cases t with
  | lower t => cases t <;>
      simp [ClashMachine.emitted, p.injective.eq_iff, ready, preparedLocal,
        ForestStage.initialLocal, encodeWord]
  | tokens => simp [ClashMachine.emitted, p.injective.eq_iff, ready,
      preparedLocal, ForestStage.initialLocal, tokenBits, tokenWords, encodeWords]
  | records => simp [ClashMachine.emitted, p.injective.eq_iff, ready,
      preparedLocal, ForestStage.initialLocal]
  | rootTable => simp [ClashMachine.emitted, p.injective.eq_iff, ready,
      preparedLocal, ForestStage.initialLocal]

theorem result_emitted (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) (tokens : List Token) :
    result p (ClashMachine.emitted (p .tokens) (p (.lower .remaining)) base tokens)
        V input = result p base V input := by
  classical
  funext k
  by_cases inside : ∃ t, p t = k
  · obtain ⟨t, rfl⟩ := inside
    simp only [result, ForestPlacement.fill_at]
  · have outside : ∀ t, p t ≠ k := not_exists.mp inside
    rw [result, ForestPlacement.fill_other p _ _ k outside,
      result, ForestPlacement.fill_other p _ _ k outside]
    exact ClashMachine.emitted_other (p .tokens) (p (.lower .remaining)) k
      (Ne.symm (outside .tokens)) (Ne.symm (outside (.lower .remaining))) base tokens

theorem lowerTrace (p : Ports K) (labels : ForestStage.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (code : ∀ l, program (labels l) = ForestStage.statement p labels exit l)
    (base : K → List Bool) (V : NPVerifier) (input : List Bool)
    (ready : Prepared p base V input) (ambient : σ × Bool) :
    (advance (TM2.step program))^[lowerSteps V input]
      (some ⟨some (labels .reverseTokens), (ambient, none), base⟩) =
      some ⟨exit, (ambient, none), result p base V input⟩ := by
  have h := ForestStage.traceAt p labels exit program code base ambient
    (InitializationTemplate.initializationTokens V input) (freeInputs V input)
    (ProducerInvariant.next (VerifierCircuit.initialFrame V input))
    (ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input)).reverse
    (initialGates V input) [] [] (initialCompile V input)
  have hprepared : ForestPlacement.fill p base (preparedLocal V input) = base := by
    rw [show preparedLocal V input = (fun t => base (p t)) from funext fun t => (ready t).symm]
    exact ForestPlacement.fill_self p base
  rw [finalLocal_eq] at h
  change (advance (TM2.step program))^[lowerSteps V input]
    (some ⟨some (labels .reverseTokens), (ambient, none),
      ForestPlacement.fill p base (preparedLocal V input)⟩) =
    some ⟨exit, (ambient, none), result p base V input⟩ at h
  simpa only [hprepared] using h

omit [DecidableEq K] in
theorem result_at (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) (t : ForestStage.Tape) :
    result p base V input (p t) = finishedLocal V input t :=
  ForestPlacement.fill_at p base _ t

omit [DecidableEq K] in
theorem result_other (p : Ports K) (base : K → List Bool) (V : NPVerifier)
    (input : List Bool) (k : K) (outside : ∀ t, p t ≠ k) :
    result p base V input k = base k :=
  ForestPlacement.fill_other p base _ k outside

def lowerTimePolynomial (V : NPVerifier) : Polynomial Nat :=
  ForestStage.timePolynomial.comp
    (ProducerInvariant.budgetPolynomial V + ProducerInvariant.tapePolynomial V + 1)

theorem lowerSteps_le (V : NPVerifier) (input : List Bool) :
    lowerSteps V input ≤ (lowerTimePolynomial V).eval input.length := by
  have roots := ProducerInvariant.step_roots
    (Frame.initial (id : Fin (freeInputs V input) → Fin (freeInputs V input)))
    (VerifierCircuit.initialExpressions V input)
  have h := ForestStage.forest_steps_le Fin.val
    (List.ofFn (VerifierCircuit.initialExpressions V input)) (freeInputs V input) []
    (fun i => i.isLt)
  have rootEq : ProducerInvariant.rootValues (VerifierCircuit.initialFrame V input) =
      Batch.roots (freeInputs V input)
        (List.ofFn (VerifierCircuit.initialExpressions V input)) := by
    simpa [ProducerInvariant.snapshot, ProducerInvariant.rootValues,
      VerifierCircuit.initialFrame, Frame.initial, Fragment.empty, freeInputs] using roots
  have hsteps : lowerSteps V input ≤ ForestStage.timePolynomial.eval
      (freeInputs V input + Batch.cost (List.ofFn (VerifierCircuit.initialExpressions V input)) +
        (tokenBits (InitializationTemplate.initializationTokens V input)).length + 1) := by
    simpa only [lowerSteps, InitializationTemplate.initializationTokens_eq, rootEq,
      initialGates, List.length_nil, Nat.add_zero] using h
  have hg := VerifierCircuit.circuitOfVerifier_gates_le_polynomial V input
  rw [VerifierCircuit.circuitOfVerifier_gate_count] at hg
  have hb := ProducerInvariant.budgetPolynomial_eval V input
  have ht := ProducerInvariant.initial_tokens_length_le V input
  rw [← InitializationTemplate.initializationTokens_eq] at ht
  have sizeBound : freeInputs V input +
      Batch.cost (List.ofFn (VerifierCircuit.initialExpressions V input)) +
      (tokenBits (InitializationTemplate.initializationTokens V input)).length + 1 ≤
      (ProducerInvariant.budgetPolynomial V + ProducerInvariant.tapePolynomial V + 1).eval
        input.length := by
    simp only [Polynomial.eval_add, Polynomial.eval_one]
    dsimp only [freeInputs]
    omega
  exact hsteps.trans (by
    rw [lowerTimePolynomial, Polynomial.eval_comp]
    exact natPolynomial_eval_mono ForestStage.timePolynomial sizeBound)

abbrev Label (V : NPVerifier) := InitializationAssembly.Label V ⊕ ForestStage.Label

def entry (V : NPVerifier) : Label V := .inl .control

def emitLabels {V : NPVerifier} (labels : Label V ↪ Λ) :
    InitializationAssembly.Label V ↪ Λ :=
  ⟨fun l => labels (.inl l), fun _ _ h => Sum.inl.inj (labels.injective h)⟩

def statement (V : NPVerifier) (p : FullPorts K) (labels : Label V ↪ Λ)
    (exit : Option Λ) : Label V → TM2.Stmt (fun _ : K => Bool) Λ (State σ)
  | .inl l => InitializationAssembly.statement V p.emit (emitLabels labels)
      (some (labels (.inr .reverseTokens))) l
  | .inr l => ForestStage.statement p.lower (fun l => labels (.inr l)) exit l

def Agrees (V : NPVerifier) (p : FullPorts K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ)) : Prop :=
  ∀ l, program (labels l) = statement V p labels exit l

structure FullReady (V : NPVerifier) (p : FullPorts K) (base : K → List Bool)
    (input : List Bool) : Prop where
  emitter : InitializationAssembly.Ready V p.emit base input
  lowerer : Ready p.lower base V input

def steps (V : NPVerifier) (input : List Bool) : Nat :=
  InitializationAssembly.steps V input + lowerSteps V input

theorem trace (V : NPVerifier) (p : FullPorts K) (labels : Label V ↪ Λ)
    (exit : Option Λ) (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V p labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : FullReady V p base input) (ambient : σ) :
    (advance (TM2.step program))^[steps V input]
      (some ⟨some (labels (entry V)), ClashMachine.clean ambient, base⟩) =
      some ⟨exit, ClashMachine.clean ambient, result p.lower base V input⟩ := by
  have first := InitializationAssembly.trace V p.emit (emitLabels labels)
    (some (labels (.inr .reverseTokens))) program (fun l => ha (.inl l))
    base input ready.emitter ambient
  rw [p.output_shared, p.count_shared] at first
  have second := lowerTrace p.lower (fun l => labels (.inr l)) exit program
    (fun l => ha (.inr l))
    (ClashMachine.emitted (p.lower .tokens) (p.lower (.lower .remaining)) base
      (InitializationTemplate.initializationTokens V input)) V input
    (prepared_emitted p.lower base V input ready.lowerer) (ambient, false)
  rw [result_emitted] at second
  exact ClashMachine.chain first second

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  InitializationAssembly.timePolynomial V + lowerTimePolynomial V

theorem steps_le_timePolynomial (V : NPVerifier) (input : List Bool) :
    steps V input ≤ (timePolynomial V).eval input.length := by
  simpa only [steps, timePolynomial, Polynomial.eval_add] using
    Nat.add_le_add (InitializationAssembly.steps_le_timePolynomial V input)
      (lowerSteps_le V input)

def verifierPlacedInPolynomialTime (V : NPVerifier) (p : FullPorts K)
    (labels : Label V ↪ Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State σ))
    (ha : Agrees V p labels exit program) (base : K → List Bool) (input : List Bool)
    (ready : FullReady V p base input) (ambient : σ) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), ClashMachine.clean ambient, base⟩
      (some ⟨exit, ClashMachine.clean ambient, result p.lower base V input⟩)
      ((timePolynomial V).eval input.length) where
  steps := steps V input
  evals_in_steps := trace V p labels exit program ha base input ready ambient
  steps_le_m := steps_le_timePolynomial V input

end BinPackingGames.Foundations.Complexity.CookLevin.InitializationStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs

open ProducerInvariant ProducerArena

theorem boundary_view (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot) :
    (fun t => boundary V input remaining s (transitionPorts V t)) =
      TransitionArena.tapes (localBase V input) (VerifierCircuit.capacity V input.length) remaining s := by
  funext t
  exact ForestPlacement.fill_at _ _ _ t

theorem boundary_other (V : NPVerifier) (input : List Bool) (remaining : Nat) (s : Snapshot)
    (k : Tape V) (outside : ∀ t, transitionPorts V t ≠ k) :
    boundary V input remaining s k = bootstrapPrepared V input k :=
  ForestPlacement.fill_other _ _ _ k outside

theorem finished_private (V : NPVerifier) (input : List Bool) (s : Snapshot)
    (w : Work) (outside : ∀ t, transitionPorts V t ≠ .inr w) :
    finished V input s (.inr w) = [] := by
  rw [finished_other V input s _ outside,
    bootstrapPrepared_other V input _
      (Ne.symm (outside (.inl (.lower .current))))
      (Ne.symm (outside (.inl (.lower .remaining))))
      (Ne.symm (outside (.inr .cursor)))]
  rfl

theorem private_finish_outside (V : NPVerifier) (f : CircuitFinish.Tape) :
    ∀ t, transitionPorts V t ≠ .inr (.finish f) := by
  intro t
  cases t with
  | inl t => simp [transitionTape]
  | inr t => cases t <;> simp [transitionTape, raw, q, capacity, countdown, clock]

theorem bootstrap_work (V : NPVerifier) (input : List Bool) (w : Work)
    (hc : (.inr w : Tape V) ≠ current V) (hn : (.inr w : Tape V) ≠ count V)
    (hz : (.inr w : Tape V) ≠ cursor V) : bootstrapPrepared V input (.inr w) = [] := by
  rw [bootstrapPrepared_other V input _ hc hn hz]
  rfl

theorem bootstrap_extra (V : NPVerifier) (input : List Bool) (s : Snapshot)
    (e : TransitionArena.Extra) :
    localBase V input (.inr e) =
      TransitionArena.tapes (localBase V input) (VerifierCircuit.capacity V input.length)
        (V.horizon input.length) s (.inr e) := by
  cases e <;> simp only [TransitionArena.tapes]
  all_goals first
    | rfl
    | exact bootstrapPrepared_cursor V input
    | exact bootstrap_clock V input .capacity
    | exact bootstrap_clock V input .horizon

theorem initial_result_view (V : NPVerifier) (input : List Bool) :
    (fun t => InitializationStage.result (forestPorts V) (bootstrapPrepared V input) V input
      (transitionPorts V t)) =
      TransitionArena.tapes (localBase V input) (VerifierCircuit.capacity V input.length)
        (V.horizon input.length) (snapshot (VerifierCircuit.initialFrame V input)) := by
  funext t
  cases t with
  | inl t =>
    change InitializationStage.result (forestPorts V) _ V input (forestPorts V t) = _
    rw [InitializationStage.result_at]
    cases t with
    | lower t => cases t <;> rfl
    | tokens => rfl
    | records => rfl
    | rootTable => rfl
  | inr e =>
    have outside : ∀ t, forestPorts V t ≠ transitionPorts V (.inr e) := by
      intro t h
      change transitionPorts V (.inl t) = transitionPorts V (.inr e) at h
      have impossible := (transitionPorts V).injective h
      cases impossible
    rw [InitializationStage.result_other _ _ _ _ _ outside]
    exact bootstrap_extra V input _ e

theorem initial_result_eq_boundary (V : NPVerifier) (input : List Bool) :
    InitializationStage.result (forestPorts V) (bootstrapPrepared V input) V input =
      boundary V input (V.horizon input.length) (snapshot (VerifierCircuit.initialFrame V input)) := by
  classical
  funext k
  by_cases inside : ∃ t, transitionPorts V t = k
  · obtain ⟨t, rfl⟩ := inside
    exact (congrFun (initial_result_view V input) t).trans
      (congrFun (boundary_view V input _ _) t).symm
  · have outside := not_exists.mp inside
    have outsideForest : ∀ t, forestPorts V t ≠ k := fun t => outside (.inl t)
    rw [InitializationStage.result_other _ _ _ _ _ outsideForest,
      boundary_other V input _ _ _ outside]

theorem clock_outside (V : NPVerifier) (c : ClockPreparation.Clock)
    (hq : c ≠ .witness) (hS : c ≠ .capacity) (hT : c ≠ .horizon) :
    ∀ t, transitionPorts V t ≠ clock V c := by
  intro t
  cases t with
  | inl t => simp [transitionTape, clock]
  | inr e =>
    cases e with
    | q => change clock V .witness ≠ clock V c; simpa only [ne_eq, clock_eq_iff] using Ne.symm hq
    | capacity => change clock V .capacity ≠ clock V c; simpa only [ne_eq, clock_eq_iff] using Ne.symm hS
    | countdown => change clock V .horizon ≠ clock V c; simpa only [ne_eq, clock_eq_iff] using Ne.symm hT
    | raw => exact raw_ne_clock V c
    | cursor | position | address | value | scratch | copy | saveLeft | saveRight =>
      simp [transitionTape, clock]

theorem freeInputs_outside (V : NPVerifier) : ∀ t, transitionPorts V t ≠ freeInputs V :=
  clock_outside V .inputCount (by decide) (by decide) (by decide)

@[simp] theorem finished_freeInputs (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    finished V input s (freeInputs V) = encodeWord (2 * V.witnessBound.eval input.length + 1) := by
  rw [finished_other V input s _ (freeInputs_outside V)]
  exact bootstrap_clock V input .inputCount

theorem finish_view (V : NPVerifier) (input : List Bool) (s : Snapshot) :
    (fun t => finished V input s (finishPorts V t)) =
      CircuitFinish.memory s.currentBits
        (encodeWord (2 * V.witnessBound.eval input.length + 1)) s.rootBits s.reversedRecords [] [] [] := by
  funext t
  cases t with
  | current => exact finished_current V input s
  | freeInputs => exact finished_freeInputs V input s
  | root => exact finished_roots V input s
  | reversedRecords => exact finished_records V input s
  | output => exact finished_private V input s _ (private_finish_outside V .output)
  | gateCount => exact finished_private V input s _ (private_finish_outside V .gateCount)
  | scratch => exact finished_private V input s _ (private_finish_outside V .scratch)

theorem circuitFinish_view (V : NPVerifier) (input : List Bool) :
    (fun t => finished V input (snapshot (finalFrame V input)) (finishPorts V t)) =
      CircuitFinish.initialTapes (VerifierCircuit.circuitOfVerifier V input).wires
        (VerifierCircuit.circuitOfVerifier V input).inputs
        (VerifierCircuit.circuitOfVerifier V input).output.val
        (recordsBits (VerifierCircuit.circuitOfVerifier V input).records) := by
  rw [finish_view]
  rw [← finalFrame_circuit V input]
  simp [CircuitFinish.initialTapes, snapshot, Snapshot.currentBits, Snapshot.rootBits,
    CircuitBatch.Frame.toCircuit, CircuitBatch.Fragment.toCircuit, Circuit.wires,
    List.ofFn_succ, Circuit.records, encodeWords]

theorem bootstrap_emitter_ready (V : NPVerifier) (input : List Bool) :
    InitializationAssembly.Ready V (initializationPorts V)
      (bootstrapPrepared V input) input := by
  constructor
  · exact congrFun (bootstrap_initialization_view V input) .rawInput
  · exact congrFun (bootstrap_initialization_view V input) .framedInput
  · exact congrFun (bootstrap_initialization_view V input) .witnessBound
  · exact congrFun (bootstrap_initialization_view V input) .capacity
  · intro j
    exact congrFun (bootstrap_initialization_view V input) (.cellWork j)
  · intro j
    exact congrFun (bootstrap_initialization_view V input) (.validityWork j)

theorem bootstrap_lowerer_ready (V : NPVerifier) (input : List Bool) :
    InitializationStage.Ready (forestPorts V) (bootstrapPrepared V input) V input := by
  intro t
  cases t with
  | lower t =>
    cases t <;> simp only [ForestStage.initialLocal]
    all_goals first
      | exact bootstrapPrepared_current V input
      | exact bootstrapPrepared_count V input
      | apply bootstrap_work <;> simp [current, count, cursor, shared, TransitionArena.forestPorts]
  | tokens =>
    apply bootstrap_work <;> simp [current, count, cursor, shared, TransitionArena.forestPorts]
  | records =>
    apply bootstrap_work <;> simp [current, count, cursor, shared, TransitionArena.forestPorts]
  | rootTable =>
    apply bootstrap_work <;> simp [current, count, cursor, shared, TransitionArena.forestPorts]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerHandoffs

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerTailStage

open Turing ProducerArena ProducerInvariant ProducerHandoffs

local instance completenessLabelFintype (V : NPVerifier) :
    Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance completenessStateFintype (V : NPVerifier) :
    Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance completenessAlphabetFintype (V : NPVerifier) :
    ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance completenessLabelDecidableEq (V : NPVerifier) :
    DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance completenessStateDecidableEq (V : NPVerifier) :
    DecidableEq V.computation.tm.σ := Classical.decEq _
local instance completenessAlphabetDecidableEq (V : NPVerifier) :
    ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

abbrev IterateLabel (V : NPVerifier) :=
  TransitionIteration.Label (VerifierCircuit.indexing V) V.computation.tm.m
abbrev Label (V : NPVerifier) :=
  IterateLabel V ⊕ (AcceptanceStage.Label V ⊕ CircuitFinish.Label)

def entry (V : NPVerifier) : Label V :=
  .inl (TransitionIteration.entry (VerifierCircuit.indexing V) V.computation.tm.m)

def statement {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ) :
    Label V → TM2.Stmt (Alphabet V) Λ State
  | .inl l => ForestPlacement.statement (transitionPorts V)
      (fun l => labels (.inl l)) (some (labels (.inr (.inl (AcceptanceStage.entry V)))))
      (TransitionIteration.program (VerifierCircuit.indexing V) V.computation.tm.m l)
  | .inr (.inl l) => ForestPlacement.statement (transitionPorts V)
      (fun l => labels (.inr (.inl l))) (some (labels (.inr (.inr .copyOut))))
      (AcceptanceStage.program V l)
  | .inr (.inr l) => ForestPlacement.statement (finishPorts V)
      (fun l => labels (.inr (.inr l))) exit (CircuitFinish.program (σ := Unit × Bool) l)

def initial (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  boundary V input (V.horizon input.length) (snapshot (VerifierCircuit.initialFrame V input))

def afterIteration (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  finished V input (snapshot (VerifierCircuit.timeFrame V input (V.horizon input.length)))

def afterAcceptance (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  finished V input (snapshot (ProducerInvariant.finalFrame V input))

def terminal (V : NPVerifier) (input : List Bool) : Tape V → List Bool :=
  ForestPlacement.fill (finishPorts V) (afterAcceptance V input)
    (CircuitFinish.verifierFinalTapes V input)

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  ProducerTime.iterationPolynomial V +
    (ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V) +
    ProducerTime.finishPolynomial V

theorem finish_entry (V : NPVerifier) (input : List Bool) :
    ForestPlacement.fill (finishPorts V) (afterAcceptance V input)
      (CircuitFinish.verifierInitialTapes V input) = afterAcceptance V input := by
  have h := circuitFinish_view V input
  change (fun t => afterAcceptance V input (finishPorts V t)) =
    CircuitFinish.verifierInitialTapes V input at h
  rw [← h, ForestPlacement.fill_self]

def inTime {Λ : Type} (V : NPVerifier) (labels : Label V → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet V) Λ State)
    (code : ∀ l, program (labels l) = statement V labels exit l)
    (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initial V input⟩
      (some ⟨exit, initialState, terminal V input⟩)
      ((timePolynomial V).eval input.length) := by
  have iter := TransitionIteration.verifierPlacedInPolynomialTime V input
    (transitionPorts V) (fun l => labels (.inl l))
    (some (labels (.inr (.inl (AcceptanceStage.entry V))))) program
    (fun l => code (.inl l)) (bootstrapPrepared V input) (localBase V input)
  have iter' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (entry V)), initialState, initial V input⟩
      (some ⟨some (labels (.inr (.inl (AcceptanceStage.entry V)))), initialState,
        afterIteration V input⟩)
      ((ProducerTime.iterationPolynomial V).eval input.length) := iter
  have accept := AcceptanceStage.verifierPlacedInPolynomialTime V input
    (transitionPorts V) (fun l => labels (.inr (.inl l)))
    (some (labels (.inr (.inr .copyOut)))) program
    (fun l => code (.inr (.inl l))) (bootstrapPrepared V input) (localBase V input)
  have accept' : StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels (.inr (.inl (AcceptanceStage.entry V)))), initialState,
        afterIteration V input⟩
      (some ⟨some (labels (.inr (.inr .copyOut))), initialState,
        afterAcceptance V input⟩)
      ((ProducerTime.acceptanceEmissionPolynomial V + ProducerTime.loweringPolynomial V).eval
        input.length) := accept
  have finish := CircuitFinish.verifierPlacedInPolynomialTime (finishPorts V)
    (fun l => labels (.inr (.inr l))) exit (afterAcceptance V input) program
    (fun l => code (.inr (.inr l))) V input ((), false) none
  rw [finish_entry] at finish
  have combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ iter' accept') finish
  simpa only [timePolynomial, Polynomial.eval_add, terminal, initialState,
    TermMachine.initialState, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

theorem terminal_output (V : NPVerifier) (input : List Bool) :
    terminal V input (output V) = circuitBits (VerifierCircuit.circuitOfVerifier V input) := by
  change ForestPlacement.fill (finishPorts V) _ _ (finishPorts V .output) = _
  rw [ForestPlacement.fill_at, CircuitFinish.verifierFinal_output]

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerTailStage

namespace BinPackingGames.Foundations.Complexity.CookLevin.ProducerMachine

open Turing ProducerArena

local instance completenessLabelFintype_r258638_2 (V : NPVerifier) :
    Fintype V.computation.tm.Λ := V.computation.tm.ΛFin
local instance completenessStateFintype_r258638_2 (V : NPVerifier) :
    Fintype V.computation.tm.σ := V.computation.tm.σFin
local instance completenessAlphabetFintype_r258638_2 (V : NPVerifier) :
    ∀ k, Fintype (V.computation.tm.Γ k) := V.finiteAlphabet
local instance completenessLabelDecidableEq_r258638_2 (V : NPVerifier) :
    DecidableEq V.computation.tm.Λ := Classical.decEq _
local instance completenessStateDecidableEq_r258638_2 (V : NPVerifier) :
    DecidableEq V.computation.tm.σ := Classical.decEq _
local instance completenessAlphabetDecidableEq_r258638_2 (V : NPVerifier) :
    ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _
abbrev Label (V : NPVerifier) :=
  ProducerFrontStage.Label V ⊕ (InitializationStage.Label V ⊕ ProducerTailStage.Label V)

def initPorts (V : NPVerifier) : InitializationStage.FullPorts (Tape V) where
  emit := initializationPorts V
  lower := forestPorts V
  output_shared := rfl
  count_shared := rfl

def initLabels (V : NPVerifier) : InitializationStage.Label V ↪ Label V :=
  ⟨fun l => .inr (.inl l), by intro a b h; exact Sum.inl.inj (Sum.inr.inj h)⟩

def entry (V : NPVerifier) : Label V := .inl (ProducerFrontStage.entry V)

def program (V : NPVerifier) : Label V → TM2.Stmt (Alphabet V) (Label V) State
  | .inl l => ProducerFrontStage.statement V Sum.inl
      (some (initLabels V (InitializationStage.entry V))) l
  | .inr (.inl l) => InitializationStage.statement V (initPorts V) (initLabels V)
      (some (.inr (.inr (ProducerTailStage.entry V)))) l
  | .inr (.inr l) => ProducerTailStage.statement V (fun l => .inr (.inr l)) none l

def timePolynomial (V : NPVerifier) : Polynomial Nat :=
  ProducerFrontStage.timePolynomial V + InitializationStage.timePolynomial V +
    ProducerTailStage.timePolynomial V

theorem initializerReady (V : NPVerifier) (input : List Bool) :
    InitializationStage.FullReady V (initPorts V) (bootstrapPrepared V input) input :=
  ⟨ProducerHandoffs.bootstrap_emitter_ready V input,
    ProducerHandoffs.bootstrap_lowerer_ready V input⟩

def inTime (V : NPVerifier) (input : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (entry V), initialState, initialTapes V input⟩
      (some ⟨none, initialState, ProducerTailStage.terminal V input⟩)
      ((timePolynomial V).eval input.length) := by
  have front := ProducerFrontStage.inTime V Sum.inl
    (some (initLabels V (InitializationStage.entry V))) (program V)
    (fun _ => rfl) input
  have init := InitializationStage.verifierPlacedInPolynomialTime V (initPorts V)
    (initLabels V) (some (.inr (.inr (ProducerTailStage.entry V))))
    (program V) (fun _ => rfl) (bootstrapPrepared V input) input
    (initializerReady V input) ()
  have init' : StateTransition.EvalsToInTime (TM2.step (program V))
      ⟨some (initLabels V (InitializationStage.entry V)), initialState, bootstrapPrepared V input⟩
      (some ⟨some (.inr (.inr (ProducerTailStage.entry V))), initialState,
        ProducerTailStage.initial V input⟩)
      ((InitializationStage.timePolynomial V).eval input.length) := by
    simpa only [initPorts, ProducerHandoffs.initial_result_eq_boundary,
      ProducerTailStage.initial, initialState, TermMachine.initialState,
      ClashMachine.clean] using init
  have tail := ProducerTailStage.inTime V (fun l => .inr (.inr l)) none
    (program V) (fun _ => rfl) input
  have combined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (StateTransition.EvalsToInTime.trans _ _ _ _ _ _ front init') tail
  simpa only [entry, timePolynomial, Polynomial.eval_add,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

def rawProgram (V : NPVerifier) : MachineCanonicalOutput.Program (Tape V) (Label V) State where
  input := raw V
  output := output V
  main := entry V
  initial := initialState
  code := program V

theorem initialCfg (V : NPVerifier) (input : List Bool) :
    initList (MachineCanonicalOutput.sourceMachine (rawProgram V)) input =
      (⟨some (entry V), initialState, initialTapes V input⟩ :
        (MachineCanonicalOutput.sourceMachine (rawProgram V)).Cfg) := by
  unfold initList
  congr 1
  funext k
  rw [initialTapes_eq]
  rfl

def terminalRun (V : NPVerifier) (input : List Bool) :
    MachineCanonicalOutput.TerminalRun (rawProgram V) input
      (circuitBits (VerifierCircuit.circuitOfVerifier V input))
      ((timePolynomial V).eval input.length) where
  state := initialState
  tapes := ProducerTailStage.terminal V input
  execution := by
    rw [initialCfg]
    exact inTime V input
  output_eq := ProducerTailStage.terminal_output V input

def cleanupTapes (V : NPVerifier) : List (Tape V) :=
  (Finset.univ.erase (output V)).toList

theorem cleanup_complete (V : NPVerifier) (k : Tape V) :
    k ∈ cleanupTapes V ↔ k ≠ (rawProgram V).output := by
  simp [cleanupTapes, rawProgram]

def computableInPolyTime (V : NPVerifier) :
    TM2ComputableInPolyTime id circuitBits (VerifierCircuit.circuitOfVerifier V) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram V) (cleanupTapes V)
    (cleanup_complete V) id circuitBits (VerifierCircuit.circuitOfVerifier V)
    (timePolynomial V) (terminalRun V)

end BinPackingGames.Foundations.Complexity.CookLevin.ProducerMachine

namespace BinPackingGames.Foundations.Complexity.CookLevin.Completeness

open Turing

def verifierReduction (V : NPVerifier) : PolynomialThreeSATReduction V.Accepts where
  reduce input := (VerifierCircuit.circuitOfVerifier V input).toFormula
  computation := MachineSequential.composeBits (ProducerMachine.computableInPolyTime V)
    CircuitProducer.computableInPolyTime
  correct input := (VerifierCircuit.circuitOfVerifier_correct V input).symm

end BinPackingGames.Foundations.Complexity.CookLevin.Completeness

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

theorem constant_exec (slot : (Reg ⊕ Fin 6) ↪ K) (destination : Reg) (constant : Nat)
    (base : K → List Bool) (values : Reg → Nat) (state : State) (width : Nat)
    (bounded : ∀ r, (values r).size ≤ width) :
    ∃ steps ≤ (runtimePolynomial (constantCommands destination constant)).eval width + 2,
      Exec (setConstant slot destination constant)
        ⟨state, registerTapes slot base values⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          registerTapes slot base (Function.update values destination constant)⟩ := by
  simpa only [setConstant, constant_result] using exec slot (constantCommands destination constant)
    base values (constant_ready destination constant values) state width bounded

end BinPackingGap.PackingAssignments

end

end OAI
end

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

theorem setInput_exec (num : Descriptor → Expr Input) (den : Expr Input)
    (destination : Input) (constant : Nat) (base : Tape num den Other Extra → List Bool)
    (input : Input → Nat) (other : Other → Nat) (state : State) (width : Nat)
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ (setInputTime (Other := Other) num den destination constant).eval width,
      Exec (setInput num den destination constant)
        ⟨state, tapes num den base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes num den base (Function.update input destination constant) other⟩ := by
  have run := PackingAssignments.constant_exec (registers (Extra := Extra) num den)
    (inputs num den destination) constant base (values num den input other) state width
    (values_width num den input other width hi ho)
  rw [← values_update_input] at run
  simpa only [setInput, setInputTime, Polynomial.eval_add, Polynomial.eval_ofNat, tapes] using run

end BinPackingGap.PackingLayoutCommands

end

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

theorem exec (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K)
    (output counter : K) (different : counter ≠ output)
    (outsideOutput : ∀ d i, slot d i ≠ output)
    (outsideCounter : ∀ d i, slot d i ≠ counter)
    (descriptors : List δ) (base : K → List Bool) (values : δ → α → Nat)
    (state : State) (width n : Nat)
    (shape : ∀ d ∈ descriptors,
      registerTapes (slot d) base (initial (numerator d) denominator (values d)) = base)
    (hwidth : ∀ d ∈ descriptors, ∀ a, (values d a).size ≤ width) :
    ∃ steps ≤ n * ((PackingChunkMachine.timePolynomial numerator denominator descriptors).eval width + 2) + 1,
      Exec (code numerator denominator slot output counter descriptors)
        ⟨state, counterTapes counter base n⟩ steps
        ⟨guardState none, outputTapes output (counterTapes counter base 0)
          (repeatRecords (PackingChunkMachine.records numerator denominator values descriptors) n)⟩ := by
  induction n generalizing base state with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      have h : PackingCountedProgram.more ((PackingCountedProgram.guard counter).eval
          ⟨state, counterTapes counter base 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [code, PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        repeatRecords, PackingChunkMachine.outputTapes_nil] using
        (Exec.loop_false (a := PackingArithmeticProgram.code
          (PackingChunkMachine.code numerator denominator slot output descriptors)) h)
  | succ n ih =>
      let word := PackingChunkMachine.records numerator denominator values descriptors
      let middle := outputTapes output base word
      have counterShape : ∀ d ∈ descriptors,
          registerTapes (slot d) (counterTapes counter base n)
            (initial (numerator d) denominator (values d)) = counterTapes counter base n := by
        intro d hd
        exact shape_after_counter (slot d) counter (outsideCounter d) base _ (shape d hd) n
      have chunkRun := PackingChunkMachine.exec numerator denominator slot output outsideOutput
        descriptors (counterTapes counter base n) values () width counterShape hwidth
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ := PackingArithmeticProgram.exec_in_time
        (PackingChunkMachine.code numerator denominator slot output descriptors)
        (counterTapes counter base n) (outputTapes output (counterTapes counter base n) word)
        ((PackingChunkMachine.timePolynomial numerator denominator descriptors).eval width)
        (guardState (some true)) chunkRun
      have middleShape : ∀ d ∈ descriptors,
          registerTapes (slot d) middle
            (initial (numerator d) denominator (values d)) = middle := by
        intro d hd
        exact PackingChunkMachine.shape_after_output (slot d) output (outsideOutput d)
          base _ (shape d hd) word
      obtain ⟨tailSteps, tailBound, tailRun⟩ :=
        ih middle (.arithmetic (BinaryAddMachine.clean ())) middleShape
      have guardTrue : PackingCountedProgram.more ((PackingCountedProgram.guard counter).eval
          ⟨state, counterTapes counter base (n + 1)⟩).state = true := by
        rw [PackingCountedProgram.guard_succ]
        rfl
      have bodyRun' : Exec
          (PackingArithmeticProgram.code
            (PackingChunkMachine.code numerator denominator slot output descriptors))
          ((PackingCountedProgram.guard counter).eval
            ⟨state, counterTapes counter base (n + 1)⟩) bodySteps
          ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes counter middle n⟩ := by
        rw [PackingCountedProgram.guard_succ]
        simpa only [output_counter_comm output counter different, middle] using bodyRun
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · simp only [Nat.add_mul, Nat.one_mul]
        omega
      · have combined := Exec.loop_true guardTrue bodyRun' tailRun
        have finalFrame : outputTapes output (counterTapes counter middle 0)
            (repeatRecords word n) =
            outputTapes output (counterTapes counter base 0) (repeatRecords word (n + 1)) := by
          change outputTapes output (counterTapes counter (outputTapes output base word) 0)
            (repeatRecords word n) = _
          rw [← output_counter_comm output counter different,
            PackingChunkMachine.outputTapes_append]
          rfl
        simpa only [code, PackingCountedProgram.loop, finalFrame, word] using combined

theorem exec_from_tapes (numerator : δ → Expr α) (denominator : Expr α)
    (slot : (d : δ) → (Reg (numerator d) denominator ⊕ Fin 6) ↪ K)
    (output counter : K) (different : counter ≠ output)
    (outsideOutput : ∀ d i, slot d i ≠ output)
    (outsideCounter : ∀ d i, slot d i ≠ counter)
    (descriptors : List δ) (base : K → List Bool) (values : δ → α → Nat)
    (state : State) (width n : Nat)
    (counterWord : base counter = List.replicate n true)
    (shape : ∀ d ∈ descriptors,
      registerTapes (slot d) base (initial (numerator d) denominator (values d)) = base)
    (hwidth : ∀ d ∈ descriptors, ∀ a, (values d a).size ≤ width) :
    ∃ steps ≤ n * ((PackingChunkMachine.timePolynomial numerator denominator descriptors).eval width + 2) + 1,
      Exec (code numerator denominator slot output counter descriptors)
        ⟨state, base⟩ steps
        ⟨guardState none, outputTapes output (counterTapes counter base 0)
          (repeatRecords (PackingChunkMachine.records numerator denominator values descriptors) n)⟩ := by
  have initialCounter : counterTapes counter base n = base := by
    unfold counterTapes
    rw [← counterWord, Function.update_eq_self]
  simpa only [initialCounter] using exec numerator denominator slot output counter different
    outsideOutput outsideCounter descriptors base values state width n shape hwidth

end BinPackingGap.PackingConstantPool

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

theorem setupPolynomial_eval (s : Nat) :
    (setupPolynomial fixed K).eval s = staticWidth
      (PackingSetupMachine.commands (parameters fixed K)) s := by
  simp only [setupPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X, staticWidth, Nat.add_assoc]

def polynomial : Polynomial Nat :=
  setupPolynomial fixed K +
    Polynomial.C (geometryCoefficient fixed K) * (Polynomial.X + 1) ^ 2 +
    Polynomial.C (GraphPackingBounds.repetitionCoefficient fixed.P K + 3) *
      (Polynomial.X + 1) +
    Polynomial.C ((geometryFactor fixed).size + 5)

theorem polynomial_eval (s : Nat) :
    (polynomial fixed K).eval s = (setupPolynomial fixed K).eval s +
      geometryCoefficient fixed K * (s + 1) ^ 2 +
      (GraphPackingBounds.repetitionCoefficient fixed.P K + 3) * (s + 1) +
      (geometryFactor fixed).size + 5 := by
  simp [polynomial]
  omega

def width (x : GraphReductionInput) : Nat := (polynomial fixed K).eval (graphBits x).length

theorem geometry_width (x : GraphReductionInput) :
    (geometryFactor fixed * (GraphPackingPreparation.repetitions fixed K x + 1) ^ x.graph.edges.length).size ≤
      width fixed K x := by
  have h := GraphPackingBounds.size_geometry_denominator_le_quadratic fixed.P K
    (treeScale fixed) x.graph.n x.graph.edges.length (graphBits x).length
    (graph_vertexCount_le_bits x) (graph_edgeCount_le_bits x)
  have heq : geometryFactor fixed * (GraphPackingPreparation.repetitions fixed K x + 1) ^ x.graph.edges.length =
      160 * (100 * (fixed.P + x.graph.n * K + 1) + 1) ^ x.graph.edges.length *
        treeScale fixed := by
    unfold geometryFactor GraphPackingPreparation.repetitions treeScale
    ring
  rw [heq]
  change _ ≤ geometryCoefficient fixed K * ((graphBits x).length + 1) ^ 2 at h
  unfold width
  rw [polynomial_eval]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at h ⊢
  omega

theorem edge_power_width (x : GraphReductionInput) (edge : Nat)
    (he : edge ≤ x.graph.edges.length) :
    ((GraphPackingPreparation.repetitions fixed K x + 1) ^ edge).size ≤ width fixed K x := by
  have h := GraphPackingBounds.size_edge_power_le_quadratic fixed.P K x.graph.n edge
    (graphBits x).length (graph_vertexCount_le_bits x) (he.trans (graph_edgeCount_le_bits x))
  unfold GraphPackingPreparation.repetitions
  unfold width
  rw [polynomial_eval]
  have hcoeff : GraphPackingBounds.repetitionCoefficient fixed.P K + 2 ≤
      geometryCoefficient fixed K := by unfold geometryCoefficient; omega
  have hm := Nat.mul_le_mul_right (((graphBits x).length + 1) ^ 2) hcoeff
  omega

theorem vertex_power_width (x : GraphReductionInput) (vertex : Nat)
    (hv : vertex ≤ x.graph.n + 1) :
    (3 ^ vertex).size ≤ width fixed K x := by
  have hn : vertex ≤ (graphBits x).length + 1 := by
    have h := graph_vertexCount_le_bits x
    omega
  have h := GraphPackingBounds.size_vertex_power_le_linear vertex ((graphBits x).length + 1) hn
  unfold width
  rw [polynomial_eval]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at h ⊢
  omega

theorem preparedWork_width (x : GraphReductionInput) :
    ∀ r, (preparedWork fixed r).size ≤ width fixed K x := by
  intro r
  cases r <;> simp only [preparedWork, Nat.size_zero]
  all_goals unfold width; rw [polynomial_eval]; omega

end BinPackingGap.GraphPackingWidths

namespace BinPackingGap.GraphPackingStockBounds

open scoped BigOperators

variable (fixed : InventoryData) (K : Nat)

theorem setupPolynomial_le (s : Nat) :
    (GraphPackingWidths.setupPolynomial fixed K).eval s ≤
      setupCoefficient fixed K * (s + 1) ^ 2 := by
  let commands := PackingSetupMachine.commands (GraphPackingRegisters.parameters fixed K)
  let c := BinaryRegisterProgram.maxConstantSize commands
  have hs : s + (c + 1) ≤ (c + 2) * (s + 1) := by nlinarith
  simp only [GraphPackingWidths.setupPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_X]
  change 2 ^ commands.length * (s + (c + 1)) ≤
    (2 ^ commands.length * (c + 2)) * (s + 1) ^ 2
  calc
    _ ≤ 2 ^ commands.length * ((c + 2) * (s + 1)) :=
      Nat.mul_le_mul_left _ hs
    _ = (2 ^ commands.length * (c + 2)) * (s + 1) := by ring
    _ ≤ _ := GraphPackingBounds.linear_le_quadratic _ s

theorem preparationPolynomial_le (s : Nat) :
    (GraphPackingWidths.polynomial fixed K).eval s ≤
      widthCoefficient fixed K * (s + 1) ^ 2 := by
  have hsetup := setupPolynomial_le fixed K s
  have hlinear := GraphPackingBounds.linear_le_quadratic
    (GraphPackingBounds.repetitionCoefficient fixed.P K + 3) s
  have hconstant := GraphPackingBounds.constant_le_quadratic
    ((GraphPackingPreparation.geometryFactor fixed).size + 5) s
  rw [GraphPackingWidths.polynomial_eval]
  unfold widthCoefficient
  nlinarith

theorem preparationWidth_le (x : GraphReductionInput) :
    GraphPackingWidths.width fixed K x ≤
      widthCoefficient fixed K * ((graphBits x).length + 1) ^ 2 :=
  preparationPolynomial_le fixed K (graphBits x).length

theorem values_width (x : GraphReductionInput) (edge : Nat)
    (he : edge ≤ x.graph.edges.length) (vinput : PackingItemExpression.Variable) :
    (PackingDescriptorExpression.values (inventory fixed K x) none edge 0 vinput).size ≤
      GraphPackingWidths.width fixed K x := by
  cases vinput with
  | vertexPower =>
      exact GraphPackingWidths.vertex_power_width fixed K x x.graph.n (by omega)
  | geometry =>
      change (160 * (GraphPackingPreparation.repetitions fixed K x + 1) ^
        x.graph.edges.length *
        IntegerPackingArithmetic.widthRadix fixed.geometryBound ^ fixed.L).size ≤ _
      have h := GraphPackingWidths.geometry_width fixed K x
      rw [GraphPackingPreparation.geometryFactor, Nat.mul_right_comm] at h
      exact h
  | labelPower =>
      simp [PackingDescriptorExpression.values, NaturalPackingNumerator.labelPower]
  | totalPower =>
      exact GraphPackingWidths.edge_power_width fixed K x x.graph.edges.length le_rfl
  | edgePower => exact GraphPackingWidths.edge_power_width fixed K x edge he
  | repetitionOne => simp [PackingDescriptorExpression.values]

end BinPackingGap.GraphPackingStockBounds

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

namespace BinPackingGap.GraphPackingPoolExec

open NatExpressionCompiler BinaryRegisterProgram FiniteTapeProgram PackingMachineBlocks
open PackingMachineLayout PackingItemExpression PackingInventoryDescriptors
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes)

open GraphPackingRegisters

variable (fixed : InventoryData) (K : Nat)

theorem pool_exec (stock : PackingSetupExpression.Output) (descriptor : ItemDescriptor fixed)
    (base : GraphPackingRegisters.Tape fixed K → List Bool)
    (input : Variable → Nat) (other : Other fixed K → Nat) (state : State) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hwidth : ∀ a, (input a).size ≤ width) :
    ∃ steps ≤ poolBudget fixed K stock descriptor other width,
      Exec (GraphPackingProgram.pool fixed K stock descriptor)
        ⟨state, tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base
              (poolWord fixed K stock descriptor input other)) input other⟩ := by
  let vals := PackingMachineLayout.values (Numerator fixed) denominator input other
  let n := other (GraphPackingProgram.otherSetup fixed K stock)
  let filledBase := counterTapes (.inr Extra.poolCounter) base n
  let filled := tapes (Numerator fixed) denominator filledBase input other
  have sourceValue : vals (countRegister fixed K (.output stock)) = n := rfl
  have workCounter : vals (work fixed K .counter) = 0 := counterZero
  have workOne : vals (work fixed K .one) = 0 := oneZero
  have workTemporary : vals (work fixed K .temporary) = 0 := temporaryZero
  obtain ⟨tallySteps, tallyBound, tallyRun⟩ := GraphPackingTapeBlocks.tally_exec fixed K
    (.output stock) .poolCounter base vals state workCounter workOne workTemporary
  simp only [sourceValue] at tallyBound
  have tallyRun' : Exec (GraphPackingProgram.tally fixed K (.output stock) .poolCounter)
      ⟨state, tapes (Numerator fixed) denominator base input other⟩ tallySteps
      ⟨.arithmetic (BinaryAddMachine.clean ()), filled⟩ := by
    simp only [sourceValue, poolEmpty, List.append_nil] at tallyRun
    simpa only [filled, filledBase, counterTapes, PackingMachineLayout.tapes,
      GraphPackingRegisters.slots, vals] using tallyRun
  have counterWord : filled (.inr .poolCounter) = List.replicate n true := by
    simp [filled, filledBase, counterTapes]
  have shape : ∀ d ∈ [descriptor],
      registerTapes (itemSlots (Numerator fixed) denominator d) filled
        (PairExpressionCompiler.initial (Numerator fixed d) denominator input) = filled := by
    intro d _
    exact item_shape (Numerator fixed) denominator filledBase input other d
  obtain ⟨poolSteps, poolBound, poolRun⟩ := PackingConstantPool.exec_from_tapes
    (Numerator fixed) denominator (itemSlots (Numerator fixed) denominator)
    (.inr Extra.reverseOutput) (.inr Extra.poolCounter)
    (by
      intro h
      have impossible : Extra.poolCounter = Extra.reverseOutput := Sum.inr.inj h
      cases impossible)
    (fun d i => itemSlots_outside (Other := Other fixed K)
      (Numerator fixed) denominator d Extra.reverseOutput i)
    (fun d i => itemSlots_outside (Other := Other fixed K)
      (Numerator fixed) denominator d Extra.poolCounter i)
    [descriptor] filled (fun _ => input) (.arithmetic (BinaryAddMachine.clean ())) width n
    counterWord shape (by intro _ _ a; exact hwidth a)
  have clearCounter : counterTapes (.inr Extra.poolCounter) filledBase 0 = base := by
    simp only [filledBase, counterTapes, List.replicate_zero, Function.update_idem]
    rw [← poolEmpty, Function.update_eq_self]
  have finalFrame : outputTapes (.inr Extra.reverseOutput)
      (counterTapes (.inr Extra.poolCounter) filled 0)
      (PackingConstantPool.repeatRecords
        (PackingChunkMachine.records (Numerator fixed) denominator (fun _ => input) [descriptor]) n) =
      tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base
          (poolWord fixed K stock descriptor input other)) input other := by
    change outputTapes (.inr Extra.reverseOutput)
      (counterTapes (.inr Extra.poolCounter)
        (tapes (Numerator fixed) denominator filledBase input other) 0) _ = _
    rw [layout_counter, clearCounter, layout_output]
    rfl
  rw [finalFrame] at poolRun
  have phases : GraphPackingProgram.PhaseRuns
      [GraphPackingProgram.tally fixed K (.output stock) .poolCounter,
        PackingConstantPool.code (Numerator fixed) denominator
          (itemSlots (Numerator fixed) denominator)
          (.inr .reverseOutput) (.inr .poolCounter) [descriptor]]
      ⟨state, tapes (Numerator fixed) denominator base input other⟩
      (tallySteps + poolSteps)
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator
          (outputTapes (.inr .reverseOutput) base
            (poolWord fixed K stock descriptor input other)) input other⟩ :=
    .cons tallyRun' (GraphPackingProgram.PhaseRuns.single poolRun)
  refine ⟨tallySteps + poolSteps + 1, ?_, ?_⟩
  · change tallySteps + poolSteps + 1 ≤ BinaryToTallyMachine.runtimeBound n +
      n * ((PackingChunkMachine.timePolynomial (Numerator fixed) denominator [descriptor]).eval width + 2) + 3
    omega
  · simpa only [GraphPackingProgram.pool] using phases.toExec

end BinPackingGap.GraphPackingPoolExec

namespace BinPackingGap.GraphPackingGlobalLoop

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open PackingMachineLayout GraphPackingProgram GraphPackingPoolExec
open PackingItemExpression (Variable denominator)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

theorem body_exec (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ a, (input a).size ≤ width) :
    ∃ steps ≤ bodyBudget fixed K other width,
      Exec (globalEdgeBody fixed K)
        ⟨state, tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (edgeWord fixed K input other))
            (Function.update input .edgePower (radix fixed K other * input .edgePower)) other⟩ := by
  let first := poolWord fixed K .edgeStock (.w, .globalEdge true) input other
  let second := poolWord fixed K .edgeStock (.w, .globalEdge false) input other
  let middle := outputTapes (.inr .reverseOutput) base first
  obtain ⟨n₁, b₁, r₁⟩ := pool_exec fixed K .edgeStock (.w, .globalEdge true)
    base input other state width counterZero oneZero temporaryZero poolEmpty hi
  have emptyMiddle : middle (.inr .poolCounter) = [] := by
    simpa [middle, outputTapes] using poolEmpty
  obtain ⟨n₂, b₂, r₂⟩ := pool_exec fixed K .edgeStock (.w, .globalEdge false)
    middle input other (.arithmetic (BinaryAddMachine.clean ())) width
    counterZero oneZero temporaryZero emptyMiddle hi
  obtain ⟨n₃, b₃, r₃⟩ := PackingVertexUpdate.general_exec
    (Numerator fixed) denominator .edgePower (otherSetup fixed K .base)
    (.inr Work.temporary) (by simp [otherSetup]) .multiply
    (outputTapes (.inr .reverseOutput) middle second) input other temporaryZero
    (.arithmetic (BinaryAddMachine.clean ()))
  have operationMultiply (a b : Nat) :
      PackingRegisterUpdate.operation .multiply a b = a * b := rfl
  have runs := PhaseRuns.cons r₁ (PhaseRuns.cons r₂ (PhaseRuns.single r₃))
  refine ⟨n₁ + (n₂ + n₃) + 1, ?_, ?_⟩
  · have square := Nat.pow_le_pow_left
      (Nat.add_le_add_right (Nat.add_le_add_left (hi .edgePower) (radix fixed K other).size) 1) 2
    have ub := b₃.trans (Nat.mul_le_mul_left 64 square)
    unfold bodyBudget
    omega
  · simpa only [globalEdgeBody, incrementEdge, operationMultiply,
      radix, middle, first, second, edgeWord, PackingChunkMachine.outputTapes_append]
      using runs.toExec

theorem exec_bounded (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (start count width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ edge, start ≤ edge → edge < start + count →
      ∀ a, (edgeInput fixed K input other edge a).size ≤ width) :
    ∃ steps ≤ count * (bodyBudget fixed K other width + 1) + 1,
      Exec (PackingCountedProgram.loop (.inr .edgeCounter) (globalEdgeBody fixed K))
        ⟨state, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (stream fixed K input other start count))
            (edgeInput fixed K input other (start + count)) other) 0⟩ := by
  induction count generalizing base start state with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      have stop : PackingCountedProgram.more ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
          ⟨state, counterTapes (.inr .edgeCounter)
            (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other) 0⟩).state = false := by
        rw [PackingCountedProgram.guard_zero]
        rfl
      simpa only [PackingCountedProgram.loop, PackingCountedProgram.guard_zero,
        stream, PackingChunkMachine.outputTapes_nil, Nat.add_zero] using
        (Exec.loop_false (a := globalEdgeBody fixed K) stop)
  | succ count ih =>
      let word := edgeWord fixed K (edgeInput fixed K input other start) other
      have poolEmpty' : counterTapes (.inr .edgeCounter) base count (.inr .poolCounter) = [] := by
        simpa [counterTapes] using poolEmpty
      obtain ⟨bodySteps, bodyBound, bodyRun⟩ := body_exec fixed K
        (counterTapes (.inr .edgeCounter) base count) (edgeInput fixed K input other start)
        other (guardState (some true)) width counterZero oneZero temporaryZero poolEmpty'
        (hi start (by omega) (by omega))
      rw [edgeInput_update, layout_counter,
        PackingConstantPool.output_counter_comm _ _ (by simp), layout_counter] at bodyRun
      have poolEmpty'' : outputTapes (.inr .reverseOutput) base word (.inr .poolCounter) = [] := by
        simpa [outputTapes] using poolEmpty
      obtain ⟨tailSteps, tailBound, tailRun⟩ := ih
        (base := outputTapes (.inr .reverseOutput) base word)
        (state := .arithmetic (BinaryAddMachine.clean ())) (start := start + 1)
        poolEmpty'' (fun edge lower upper => hi edge (by omega) (by omega))
      refine ⟨bodySteps + tailSteps + 1, ?_, ?_⟩
      · rw [Nat.succ_mul]
        omega
      · have more : PackingCountedProgram.more
            ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
              ⟨state, counterTapes (.inr .edgeCounter)
                (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other)
                (count + 1)⟩).state = true := by
          rw [PackingCountedProgram.guard_succ]
          rfl
        have bodyRun' : Exec (globalEdgeBody fixed K)
            ((PackingCountedProgram.guard (.inr .edgeCounter)).eval
              ⟨state, counterTapes (.inr .edgeCounter)
                (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other)
                (count + 1)⟩) bodySteps
            ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
              (tapes (Numerator fixed) denominator (outputTapes (.inr .reverseOutput) base word)
                (edgeInput fixed K input other (start + 1)) other) count⟩ := by
          rw [PackingCountedProgram.guard_succ]
          exact bodyRun
        have combined := Exec.loop_true more bodyRun' tailRun
        simpa only [PackingCountedProgram.loop, word, stream,
          PackingChunkMachine.outputTapes_append, Nat.add_assoc, Nat.add_comm 1 count] using combined

theorem exec (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (start count inputWidth : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ a, (input a).size ≤ inputWidth) :
    ∃ steps ≤ count * (bodyBudget fixed K other
        (aggregateWidth fixed K other inputWidth start count) + 1) + 1,
      Exec (PackingCountedProgram.loop (.inr .edgeCounter) (globalEdgeBody fixed K))
        ⟨state, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator base (edgeInput fixed K input other start) other) count⟩ steps
        ⟨guardState none, counterTapes (.inr .edgeCounter)
          (tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (stream fixed K input other start count))
            (edgeInput fixed K input other (start + count)) other) 0⟩ := by
  exact exec_bounded fixed K base input other state start count _ counterZero oneZero temporaryZero
    poolEmpty (fun edge _ upper => edgeInput_size_le fixed K input other inputWidth start count
      edge hi (Nat.le_of_lt upper))

end BinPackingGap.GraphPackingGlobalLoop

namespace BinPackingGap.GraphPackingGlobalPhases

open FiniteTapeProgram PackingMachineBlocks GraphPackingRegisters
open PackingMachineLayout GraphPackingProgram GraphPackingPoolExec
open PackingItemExpression (Variable denominator)
open PackingItemBlockMachine (outputTapes)
open PackingCountedProgram (counterTapes guardState)

variable (fixed : InventoryData) (K : Nat)

theorem pool_runs (pools : List (Pool fixed)) (base : GraphPackingRegisters.Tape fixed K → List Bool)
    (input : Variable → Nat) (other : Other fixed K → Nat) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ a, (input a).size ≤ width) :
    ∃ steps ≤ poolListBudget fixed K pools other width,
      PhaseRuns (pools.map (fun p => GraphPackingProgram.pool fixed K p.1 p.2))
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (poolListWord fixed K pools input other))
            input other⟩ := by
  induction pools generalizing base with
  | nil =>
      refine ⟨0, by simp [poolListBudget], ?_⟩
      simpa only [List.map_nil, poolListWord, List.flatMap_nil,
        PackingChunkMachine.outputTapes_nil] using
        (PhaseRuns.nil ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator base input other⟩)
  | cons p rest ih =>
      let word := poolWord fixed K p.1 p.2 input other
      let middle := outputTapes (.inr .reverseOutput) base word
      obtain ⟨headSteps, headBound, headRun⟩ := pool_exec fixed K p.1 p.2 base input other
        (.arithmetic (BinaryAddMachine.clean ())) width counterZero oneZero temporaryZero poolEmpty hi
      have poolEmpty' : middle (.inr .poolCounter) = [] := by
        simpa [middle, outputTapes] using poolEmpty
      obtain ⟨tailSteps, tailBound, tailRun⟩ := ih middle poolEmpty'
      refine ⟨headSteps + tailSteps, ?_, ?_⟩
      · simpa only [poolListBudget, List.map_cons, List.sum_cons] using
          Nat.add_le_add headBound tailBound
      · simpa only [List.map_cons, poolListWord, List.flatMap_cons, middle, word,
          PackingChunkMachine.outputTapes_append] using PhaseRuns.cons headRun tailRun

theorem flags_exec (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ flagsBudget fixed K other width,
      Exec (GraphPackingProgram.flags fixed K)
        ⟨state, tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base
              (poolListWord fixed K (flagPools fixed) (flagInput input) other))
            (flagInput input) other⟩ := by
  have hi' : ∀ a, (input a).size ≤ width + 1 := fun a => (hi a).trans (Nat.le_succ _)
  have ho' : ∀ a, (other a).size ≤ width + 1 := fun a => (ho a).trans (Nat.le_succ _)
  obtain ⟨resetSteps, resetBound, resetRun⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .edgePower 1 base input other state (width + 1) hi' ho'
  have afterWidth : ∀ a, (flagInput input a).size ≤ width + 1 :=
    update_width input (width + 1) hi' .edgePower 1 (by simp [Nat.size_one])
  obtain ⟨poolSteps, poolBound, poolRun⟩ := pool_runs fixed K (flagPools fixed)
    base (flagInput input) other (width + 1) counterZero oneZero temporaryZero poolEmpty afterWidth
  refine ⟨resetSteps + poolSteps + 1, ?_, ?_⟩
  · unfold flagsBudget
    omega
  · simpa only [GraphPackingProgram.flags, GraphPackingProgram.setItem, flagPools,
      List.map_cons, List.map_nil, flagInput] using (PhaseRuns.cons resetRun poolRun).toExec

theorem globals_exec (base : GraphPackingRegisters.Tape fixed K → List Bool) (input : Variable → Nat)
    (other : Other fixed K → Nat) (state : State) (width : Nat)
    (counterZero : other (.inr .counter) = 0)
    (oneZero : other (.inr .one) = 0)
    (temporaryZero : other (.inr .temporary) = 0)
    (poolEmpty : base (.inr .poolCounter) = [])
    (edgeEmpty : base (.inr .edgeCounter) = [])
    (hi : ∀ a, (input a).size ≤ width) (ho : ∀ a, (other a).size ≤ width) :
    ∃ steps ≤ globalsBudget fixed K other width,
      Exec (GraphPackingProgram.globals fixed K)
        ⟨state, tapes (Numerator fixed) denominator base input other⟩ steps
        ⟨.arithmetic (BinaryAddMachine.clean ()),
          tapes (Numerator fixed) denominator
            (outputTapes (.inr .reverseOutput) base (globalsWord fixed K input other))
            (globalsInput fixed K input other) other⟩ := by
  let input₁ := Function.update input .labelPower 0
  let input₂ := Function.update input₁ .repetitionOne 0
  let finalInput := unitInput input
  have hi' : ∀ a, (input a).size ≤ width + 1 := fun a => (hi a).trans (Nat.le_succ _)
  have ho' : ∀ a, (other a).size ≤ width + 1 := fun a => (ho a).trans (Nat.le_succ _)
  have hi₁ : ∀ a, (input₁ a).size ≤ width + 1 := update_width input _ hi' .labelPower 0 (by simp)
  have hi₂ : ∀ a, (input₂ a).size ≤ width + 1 := update_width input₁ _ hi₁ .repetitionOne 0 (by simp)
  have hi₃ : ∀ a, (finalInput a).size ≤ width + 1 :=
    update_width input₂ _ hi₂ .edgePower 1 (by simp [Nat.size_one])
  obtain ⟨n₁, b₁, r₁⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .labelPower 0 base input other state (width + 1) hi' ho'
  obtain ⟨n₂, b₂, r₂⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .repetitionOne 0 base input₁ other
    (.arithmetic (BinaryAddMachine.clean ())) (width + 1) hi₁ ho'
  obtain ⟨n₃, b₃, r₃⟩ := PackingLayoutCommands.setInput_exec
    (Numerator fixed) denominator .edgePower 1 base input₂ other
    (.arithmetic (BinaryAddMachine.clean ())) (width + 1) hi₂ ho'
  let unitWord := poolListWord fixed K (unitPools fixed) finalInput other
  let middle := outputTapes (.inr .reverseOutput) base unitWord
  obtain ⟨np, bp, rp⟩ := pool_runs fixed K (unitPools fixed) base finalInput other (width + 1)
    counterZero oneZero temporaryZero poolEmpty hi₃
  let vals := values (Numerator fixed) denominator finalInput other
  obtain ⟨nt, bt, rt⟩ := GraphPackingTapeBlocks.tally_exec fixed K (.input .m) .edgeCounter
    middle vals (.arithmetic (BinaryAddMachine.clean ())) counterZero oneZero temporaryZero
  have middleEdge : middle (.inr .edgeCounter) = [] := by
    simpa [middle, outputTapes] using edgeEmpty
  have middlePool : middle (.inr .poolCounter) = [] := by
    simpa [middle, outputTapes] using poolEmpty
  have atZero : GraphPackingGlobalLoop.edgeInput fixed K finalInput other 0 = finalInput := by
    unfold GraphPackingGlobalLoop.edgeInput
    simp only [Nat.pow_zero]
    change Function.update (Function.update input₂ .edgePower 1) .edgePower 1 = _
    rw [Function.update_idem]
    rfl
  have countValue : vals (countRegister fixed K (.input .m)) = globalCount fixed K other := rfl
  have rt' : Exec (tally fixed K (.input .m) .edgeCounter)
      ⟨.arithmetic (BinaryAddMachine.clean ()), tapes (Numerator fixed) denominator middle finalInput other⟩ nt
      ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
        (tapes (Numerator fixed) denominator middle finalInput other) (globalCount fixed K other)⟩ := by
    rw [GraphPackingPoolExec.layout_counter]
    simp only [countValue, middleEdge, List.append_nil] at rt
    simpa only [PackingMachineLayout.tapes, GraphPackingRegisters.slots, vals,
      counterTapes] using rt
  obtain ⟨nl, bl, rl⟩ := GraphPackingGlobalLoop.exec fixed K middle finalInput other
    (.arithmetic (BinaryAddMachine.clean ())) 0 (globalCount fixed K other) (width + 1)
    counterZero oneZero temporaryZero middlePool hi₃
  rw [atZero] at rl
  have finalCounter : counterTapes (.inr .edgeCounter)
      (tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) middle
          (GraphPackingGlobalLoop.stream fixed K finalInput other 0 (globalCount fixed K other)))
        (globalsInput fixed K input other) other) 0 =
      tapes (Numerator fixed) denominator
        (outputTapes (.inr .reverseOutput) base (globalsWord fixed K input other))
        (globalsInput fixed K input other) other := by
    have words : outputTapes (.inr .reverseOutput) middle
        (GraphPackingGlobalLoop.stream fixed K finalInput other 0 (globalCount fixed K other)) =
        outputTapes (.inr .reverseOutput) base (globalsWord fixed K input other) := by
      dsimp only [middle, unitWord, globalsWord, finalInput]
      rw [PackingChunkMachine.outputTapes_append]
    rw [words]
    unfold counterTapes
    rw [List.replicate_zero, Function.update_eq_self_iff]
    simp [outputTapes, edgeEmpty]
  have atCount : GraphPackingGlobalLoop.edgeInput fixed K finalInput other
      (globalCount fixed K other) = globalsInput fixed K input other := rfl
  have rl' : Exec (PackingCountedProgram.loop (.inr .edgeCounter) (globalEdgeBody fixed K))
      ⟨.arithmetic (BinaryAddMachine.clean ()), counterTapes (.inr .edgeCounter)
        (tapes (Numerator fixed) denominator middle finalInput other) (globalCount fixed K other)⟩ nl
      ⟨.arithmetic (BinaryAddMachine.clean ()),
        tapes (Numerator fixed) denominator
          (outputTapes (.inr .reverseOutput) base (globalsWord fixed K input other))
          (globalsInput fixed K input other) other⟩ := by
    rw [Nat.zero_add, atCount, finalCounter] at rl
    simpa only [guardState, BinaryAddMachine.clean, BinaryAddMachine.state] using rl
  have runs := PhaseRuns.cons r₁ (PhaseRuns.cons r₂ (PhaseRuns.cons r₃
    (rp.append (PhaseRuns.cons rt' (PhaseRuns.single rl')))))
  refine ⟨n₁ + (n₂ + (n₃ + (np + (nt + nl)))) + 1, ?_, ?_⟩
  · rw [countValue] at bt
    unfold globalsBudget resetBudget
    omega
  · simpa only [GraphPackingProgram.globals, GraphPackingProgram.setItem, unitPools,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      using runs.toExec

end BinPackingGap.GraphPackingGlobalPhases

namespace BinPackingGap.GraphPackingGlobalSemantics

open GraphPackingRegisters GraphPackingPreparation
open PackingDescriptorExpression PackingInventoryDescriptors GraphPackingStockStreams
open GraphPackingPoolExec GraphPackingGlobalPhases
open PackingItemExpression (Variable denominator)

variable (fixed : InventoryData) (K : Nat)

theorem prepared_output (x : GraphReductionInput) (o : PackingSetupExpression.Output) :
    preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K o) =
      PackingSetupExpression.inventoryOutput (inventory fixed K x) o := by
  change PackingSetupExpression.outputValues (parameters fixed K)
    x.graph.n x.graph.edges.length x.k o = _
  exact congrFun (PackingSetupExpression.outputValues_eq_inventory (parameters fixed K)
    (inventory fixed K x) rfl rfl rfl rfl) o

theorem prepared_flagStock (x : GraphReductionInput) (species : FlagSpecies) :
    preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K (flagOutput species)) =
      (inventory fixed K x).flagStock species := by
  rw [prepared_output]
  cases species <;> rfl

theorem prepared_radix (x : GraphReductionInput) :
    GraphPackingGlobalLoop.radix fixed K (preparedOther fixed K x) =
      (inventory fixed K x).R + 1 := rfl

theorem flagInput_values (x : GraphReductionInput) (edge : Nat) :
    flagInput (values (inventory fixed K x) none edge 0) =
      values (inventory fixed K x) none 0 0 := by
  funext vinput
  cases vinput <;> simp [flagInput, values]

theorem poolWord_flag (x : GraphReductionInput) (species : FlagSpecies) :
    poolWord fixed K (flagOutput species) (flagDescriptor (inventory fixed K x) species)
      (values (inventory fixed K x) none 0 0) (preparedOther fixed K x) =
      rawRecords (flagPoolStream (inventory fixed K x) species) := by
  unfold poolWord
  rw [prepared_flagStock]
  have hnum : numerator (inventory fixed K x) = numerator fixed := by
    funext descriptor
    exact numerator_instantiate fixed x.graph
      (GraphPackingPreparation.repetitions fixed K x) x.k descriptor
  have records := flagPool_chunk_records (inventory fixed K x) species
  rw [hnum] at records
  simpa only [Numerator, inventory, instantiate] using records

theorem flagPools_word (x : GraphReductionInput) :
    poolListWord fixed K (flagPools fixed) (values (inventory fixed K x) none 0 0)
      (preparedOther fixed K x) = rawRecords (flagStream (inventory fixed K x)) := by
  have tree := poolWord_flag fixed K x .tree
  have main := poolWord_flag fixed K x .main
  have edge := poolWord_flag fixed K x .edge
  dsimp only [flagOutput, flagDescriptor] at tree main edge
  have words := congrArg₂ (fun a b : List Bool => a ++ b) tree
    (congrArg₂ (fun a b : List Bool => a ++ b) main edge)
  simpa only [poolListWord, flagPools, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    flagStream, rawRecords, List.flatMap_append, List.append_assoc, inventory, instantiate] using words

theorem flagInput_eq (x : GraphReductionInput) :
    flagInput (values (inventory fixed K x) none x.graph.edges.length 0) =
      values (inventory fixed K x) none 0 0 :=
  flagInput_values fixed K x x.graph.edges.length

theorem flagsWord_eq (x : GraphReductionInput) :
    poolListWord fixed K (flagPools fixed)
      (flagInput (values (inventory fixed K x) none x.graph.edges.length 0))
      (preparedOther fixed K x) = rawRecords (flagStream (inventory fixed K x)) := by
  rw [flagInput_eq, flagPools_word]

end BinPackingGap.GraphPackingGlobalSemantics

namespace BinPackingGap.GraphPackingGlobalRuntime

open GraphPackingRegisters GraphPackingPreparation GraphPackingGlobalPhases
open GraphPackingPoolRuntime
open PackingItemExpression (denominator)
open BinPackingGames.Foundations.Complexity

variable (fixed : InventoryData) (K : Nat)

def edgeWidthPolynomial : Polynomial Nat :=
  adjustedWidthPolynomial fixed K +
    Polynomial.X * GraphPackingStockBounds.widthPolynomial fixed K + 1

def resetPolynomial : Polynomial Nat :=
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .labelPower 0).comp (adjustedWidthPolynomial fixed K) +
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .repetitionOne 0).comp (adjustedWidthPolynomial fixed K) +
  (PackingLayoutCommands.setInputTime (Other := Other fixed K)
    (Numerator fixed) denominator .edgePower 1).comp (adjustedWidthPolynomial fixed K)

def edgeBodyPolynomial : Polynomial Nat :=
  poolPolynomial fixed (.w, .globalEdge true)
    (GraphPackingStockBounds.stockPolynomial fixed K) (edgeWidthPolynomial fixed K) +
  poolPolynomial fixed (.w, .globalEdge false)
    (GraphPackingStockBounds.stockPolynomial fixed K) (edgeWidthPolynomial fixed K) +
  Polynomial.C 64 * (GraphPackingStockBounds.widthPolynomial fixed K +
    edgeWidthPolynomial fixed K + 1) ^ 2 + 1

def globalsPolynomial : Polynomial Nat :=
  resetPolynomial fixed K +
  poolListPolynomial fixed (unitPools fixed)
    (GraphPackingStockBounds.stockPolynomial fixed K) (adjustedWidthPolynomial fixed K) +
  tallyPolynomial Polynomial.X + Polynomial.X * (edgeBodyPolynomial fixed K + 1) + 3

theorem width_le (x : GraphReductionInput) :
    GraphPackingWidths.width fixed K x ≤
      (GraphPackingStockBounds.widthPolynomial fixed K).eval (graphBits x).length := by
  rw [GraphPackingStockBounds.widthPolynomial_eval]
  exact GraphPackingStockBounds.preparationWidth_le fixed K x

theorem adjustedWidth_le (x : GraphReductionInput) :
    GraphPackingWidths.width fixed K x + 1 ≤
      (adjustedWidthPolynomial fixed K).eval (graphBits x).length := by
  simpa only [adjustedWidthPolynomial, Polynomial.eval_add, Polynomial.eval_one] using
    Nat.add_le_add_right (width_le fixed K x) 1

theorem stockCount_le (x : GraphReductionInput) (stock : PackingSetupExpression.Output)
    (selected : stock ∈ [.upOne, .upZero, .umOne, .umZero, .edgeStock, .treeFlags, .jobFlags]) :
    preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K stock) ≤
      (GraphPackingStockBounds.stockPolynomial fixed K).eval (graphBits x).length := by
  rw [GraphPackingGlobalSemantics.prepared_output]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
  rcases selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.up true)
  · exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.up false)
  · exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.um true)
  · exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.um false)
  · have hm : 0 < x.graph.edges.length := by
      cases h : x.graph.edges with
      | nil => exact False.elim (x.nonempty h)
      | cons e rest => simp
    exact GraphPackingStockBounds.globalStock_le_polynomial fixed K x (.edge ⟨0, hm⟩ true)
  · exact GraphPackingStockBounds.flagStock_le_polynomial fixed K x .tree
  · exact GraphPackingStockBounds.flagStock_le_polynomial fixed K x .main

theorem unitCounts_le (x : GraphReductionInput) :
    ∀ pool ∈ unitPools fixed,
      preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K pool.1) ≤
        (GraphPackingStockBounds.stockPolynomial fixed K).eval (graphBits x).length := by
  intro pool hp
  simp only [unitPools, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    exact stockCount_le fixed K x _ (by simp)

theorem flagCounts_le (x : GraphReductionInput) :
    ∀ pool ∈ flagPools fixed,
      preparedOther fixed K x (GraphPackingProgram.otherSetup fixed K pool.1) ≤
        (GraphPackingStockBounds.stockPolynomial fixed K).eval (graphBits x).length := by
  intro pool hp
  simp only [flagPools, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;>
    exact stockCount_le fixed K x _ (by simp)

theorem resetBudget_le (x : GraphReductionInput) :
    resetBudget fixed K (GraphPackingWidths.width fixed K x) ≤
      (resetPolynomial fixed K).eval (graphBits x).length := by
  have h₁ := MachineComposition.natPolynomial_eval_mono
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .labelPower 0) (adjustedWidth_le fixed K x)
  have h₂ := MachineComposition.natPolynomial_eval_mono
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .repetitionOne 0) (adjustedWidth_le fixed K x)
  have h₃ := MachineComposition.natPolynomial_eval_mono
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1) (adjustedWidth_le fixed K x)
  simpa only [resetBudget, resetPolynomial, Polynomial.eval_add, Polynomial.eval_comp] using
    Nat.add_le_add (Nat.add_le_add h₁ h₂) h₃

theorem flagsBudget_le (x : GraphReductionInput) :
    flagsBudget fixed K (preparedOther fixed K x) (GraphPackingWidths.width fixed K x) ≤
      (flagsPolynomial fixed K).eval (graphBits x).length := by
  have hr := MachineComposition.natPolynomial_eval_mono
    (PackingLayoutCommands.setInputTime (Other := Other fixed K)
      (Numerator fixed) denominator .edgePower 1) (adjustedWidth_le fixed K x)
  have hp := poolListBudget_le fixed K (flagPools fixed) (preparedOther fixed K x)
    (GraphPackingWidths.width fixed K x + 1) (GraphPackingStockBounds.stockPolynomial fixed K)
    (adjustedWidthPolynomial fixed K) (graphBits x).length
    (flagCounts_le fixed K x) (adjustedWidth_le fixed K x)
  simpa only [flagsBudget, flagsPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_one] using Nat.add_le_add_right (Nat.add_le_add hr hp) 1

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

theorem setupResult_eq (input : GenericGraphTables.Table q) :
    Setup.resultTapes setupPorts (inputTapes input) input.vertices input.darts (rowsBits input) =
      setupTapes input := by
  funext tape
  cases tape <;> simp [Setup.resultTapes, setupPorts, inputTapes, setupTapes]

theorem machineInitial_eq (input : GenericGraphTables.Table q) :
    initList (Driver.machine q) (GenericGraphTables.tableBits input) =
      (⟨some (.setup .copyFirst), initial q, inputTapes input⟩ :
        TM2.Cfg Alphabet (Driver.Label q) (State q)) := by
  change (⟨some (.setup .copyFirst), initial q, _⟩ :
    TM2.Cfg Alphabet (Driver.Label q) (State q)) = _
  congr 1
  funext tape
  cases tape <;> rfl

def setupInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩)
      (6 * (GenericGraphTables.tableBits input).length + 11) := by
  have initialized : ∀ i : Fin 7, inputTapes input (setupPorts i) =
      if i = 0 then GenericGraphTables.tableBits input else [] := by
    intro i
    fin_cases i <;> rfl
  have run := Setup.tableSetupInTime setupPorts setupPorts_injective Driver.Label.setup
    (some (Driver.headerEntry q)) (Driver.program q) (Driver.program_setup q)
    (inputTapes input) input initialized (initial q).1 none
  have initialState : ((initial q).1, (none : Option Bool)) = initial q := rfl
  have result := setupResult_eq input
  unfold rowsBits at result
  rw [initialState, result] at run
  rw [machineInitial_eq]
  exact run

def initializeInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some (loopStart input)) (time (GenericGraphTables.tableBits input).length) := by
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (setupInTime input) (headerInTime input)
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have bound := run.steps_le_m
  unfold time
  omega

end BinPackingGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
end

section
-- module Solutions.OAIQ082_BP.BinPacking_PCP_PCPSourceHardness
attribute [-instance] _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalLabel _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalState _root_.OAI.BinPackingGap.ExtensionVerifierMachine.instDecidableEqLocalTape _root_.OAI.BinPackingGap.LiteralSlotGraph.instDecidableConflict _root_.OAI.BinPackingGap.Packing.instDecidableEqTableBin _root_.OAI.BinPackingGap.PackingMachineLayout.regDecidableEq _root_.OAI.BinPackingGap.PackingMachineLayout.tapeDecidableEq
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

structure Ready (input : GenericGraphTables.Table q) (e : Nat)
    (base : Tape → List Bool) : Prop where
  le_darts : e ≤ input.darts
  original : base .original = inputBits input
  cursor : base .cursor = cursorBits input e
  vertices : base .vertices = encodeWord input.vertices
  darts : base .darts = encodeWord input.darts
  counter : base .counter = encodeWord (input.darts - e)
  edge : base .edge = encodeWord e
  tail : base .tail = []
  reverseIndex : base .reverseIndex = []
  head : base .head = []
  scratch : base .scratch = []
  compareLeft : base .compareLeft = []
  compareRight : base .compareRight = []
  output : base .output = []
  reversed : base .reversed = (prefixBits input e).reverse

theorem Ready.counter_succ {input : GenericGraphTables.Table q} {e : Nat}
    {base : Tape → List Bool} (ready : Ready input e base) (he : e < input.darts) :
    base .counter = encodeWord (input.darts - (e + 1) + 1) := by
  rw [ready.counter]
  congr 1
  omega

theorem Ready.counter_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .counter = encodeWord 0 := by
  simpa only [Nat.sub_self] using ready.counter

theorem Ready.reversed_at_end {input : GenericGraphTables.Table q}
    {base : Tape → List Bool} (ready : Ready input input.darts base) :
    base .reversed = (GraphTables.tableBits (Table.build input)).reverse := by
  rw [ready.reversed, prefixBits_full]

end BinPackingGames.Foundations.PCP.AlphabetTable.LoopState

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Body

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

structure RowStepResult (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (oldRelation : GenericGraphTables.RelationTable q)
    (oldFlag : Bool) where
  tapes : Tape → List Bool
  ready : LoopState.Ready input (e.val + 1) tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some .guard, normal oldRelation oldFlag, base⟩
    (some ⟨some .guard, CompareLoop.rowState input e, tapes⟩)
    (bodyTime q (LoopState.inputBits input).length)

def guardTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update base .counter (encodeWord (input.darts - (e.val + 1)))

def parsedTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Lookup.readRowTapes .cursor .tail .reverseIndex (guardTapes input e base)
    input.rows[e] (LoopState.cursorBits input (e.val + 1))

def workingTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Lookup.headLookupTapes headPorts (parsedTapes input e base) input e

def emittedTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Emitter.resultTapes .reversed (workingTapes input e base)
    (encodeWords (EmitRows.blockWords input e))

def resultTapes (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (clearFieldsTapes (emittedTapes input e base)) .edge
    (encodeWord (e.val + 1))

theorem workingTapes_other (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) (other : Tape)
    (hcounter : other ≠ .counter) (hcursor : other ≠ .cursor)
    (htail : other ≠ .tail) (hreverse : other ≠ .reverseIndex)
    (hscan : other ≠ .scan) (hindex : other ≠ .indexScan) (hhead : other ≠ .head) :
    workingTapes input e base other = base other := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, hcounter, hcursor, htail,
    hreverse, hscan, hindex, hhead]

theorem workingTapes_tail (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .tail = encodeWord input.rows[e].tail.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

theorem workingTapes_reverse (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .reverseIndex = encodeWord input.rows[e].reverseIndex.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes]

theorem workingTapes_head (input : GenericGraphTables.Table q)
    (e : Fin input.darts) (base : Tape → List Bool) :
    workingTapes input e base .head =
      encodeWord input.rows[input.rows[e].reverseIndex].tail.val := by
  simp [workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    Lookup.headValue, Lookup.headIndex]

def incrementInTime (base : Tape → List Bool) (ambient : Ambient q)
    (e : Nat) (he : base .edge = encodeWord e) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .increment, (ambient, none), base⟩
      (some ⟨some .guard, (ambient, none), Function.update base .edge (encodeWord (e + 1))⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (nextRow (Driver.Label.guard : Driver.Label q))
      (ambient, none) base) = _
    simpa only [List.append_nil] using congrArg some
      (stepAux_nextRow (Driver.Label.guard : Driver.Label q) (ambient, none) base e []
        (by simpa only [List.append_nil] using he))
  steps_le_m := Nat.le_refl _

theorem context_rowState (input : GenericGraphTables.Table q)
    (e : Fin input.darts) :
    context (CompareLoop.rowState input e).1 = EmitRows.rowContext input e := by
  change (input.rows[e].relation,
    decide (input.rows[e].tail.val = input.rows[input.rows[e].reverseIndex].tail.val)) =
      (input.rows[e].relation,
        decide (input.rows[e].tail = input.rows[input.rows[e].reverseIndex].tail))
  simp only [Fin.val_inj]

def emitInTime (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool)
    (operands : ∀ i, base (rowSources i) = encodeWord (EmitRows.rowValues input e i))
    (scratchEmpty : base .scratch = []) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (Driver.rowEntry q), CompareLoop.rowState input e, base⟩
      (some ⟨some (.clearField 0), CompareLoop.rowState input e,
        Emitter.resultTapes .reversed base (encodeWords (EmitRows.blockWords input e))⟩)
      (Enumeration.localCount q * (6 * (2 * 4104)) *
        (3 * ((LoopState.inputBits input).length + 1) + 3) + 1) := by
  let view := MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
    (Driver.program q)
  have sourceScratch : ∀ i : Fin 5, rowSources i ≠ Tape.scratch := by
    intro i; fin_cases i <;> decide
  have sourceOutput : ∀ i : Fin 5, rowSources i ≠ Tape.reversed := by
    intro i; fin_cases i <;> decide
  have bounded : ∀ i, EmitRows.rowValues input e i ≤ (LoopState.inputBits input).length := by
    have hn := GenericGraphTables.vertices_le_tableBits_length input
    have hm := GenericGraphTables.darts_le_tableBits_length input
    have he := e.isLt
    have ht := input.rows[e].tail.isLt
    have hh := input.rows[input.rows[e].reverseIndex].tail.isLt
    intro i
    fin_cases i <;> simp [EmitRows.rowValues, Addresses.values, LoopState.inputBits] <;> omega
  have run := EmitRows.blockInTimeAmbient input e (@context q)
    (CompareLoop.rowState input e).1 (context_rowState input e)
    rowSources Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.emit (some (.clearField 0)) view emitterView_at base operands
    scratchEmpty (LoopState.inputBits input).length bounded
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  simpa [MachineControl.configuration, emitterEquiv, Option.map_some, id_eq,
    Driver.rowEntry, Driver.rowPlan, CompareLoop.rowState, normal] using transported

theorem result_ready (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base) :
    LoopState.Ready input (e.val + 1) (resultTapes input e base) := by
  constructor
  · exact Nat.succ_le_of_lt e.isLt
  all_goals simp [resultTapes, clearFieldsTapes, emittedTapes, Emitter.resultTapes,
    workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, ready.original, ready.vertices,
    ready.darts, ready.scratch, ready.compareLeft, ready.compareRight, ready.output,
    ready.reversed, LoopState.prefixBits_reverse_succ input e.val e.isLt]

theorem workingOperands (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base) :
    ∀ i, workingTapes input e base (rowSources i) =
      encodeWord (EmitRows.rowValues input e i) := by
  intro i
  fin_cases i <;> simp [rowSources, EmitRows.rowValues, Addresses.values,
    workingTapes, Lookup.headLookupTapes, MachineLookup.tapes, headPorts,
    parsedTapes, Lookup.readRowTapes, guardTapes, Lookup.headValue, Lookup.headIndex,
    ready.vertices, ready.darts, ready.edge]

def rowStep (input : GenericGraphTables.Table q) (e : Fin input.darts)
    (base : Tape → List Bool) (ready : LoopState.Ready input e.val base)
    (oldRelation : GenericGraphTables.RelationTable q) (oldFlag : Bool) :
    RowStepResult input e base oldRelation oldFlag := by
  let N := (LoopState.inputBits input).length
  have guarded : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal oldRelation oldFlag, base⟩
      (some ⟨some .tailStart, normal oldRelation oldFlag, guardTapes input e base⟩) 1 := by
    have hbase : MachineUnaryCounter.counterTapes .counter base
        (input.darts - (e.val + 1) + 1) [] = base := by
      simp only [MachineUnaryCounter.counterTapes, List.append_nil,
        ← ready.counter_succ e.isLt, Function.update_eq_self]
    have run := MachineUnaryCounter.guardInTime_succ Tape.counter Driver.Label.guard
      .tailStart .reverseOutput (Driver.program q) (by rfl) base
      (input.darts - (e.val + 1)) [] (normal oldRelation oldFlag).1 none
    rw [hbase] at run
    simpa only [MachineUnaryCounter.counterTapes, List.append_nil, guardTapes,
      normal] using run
  have parsed : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .tailStart, normal oldRelation oldFlag, guardTapes input e base⟩
      (some ⟨some .headCopyFirst, normal input.rows[e].relation oldFlag,
        parsedTapes input e base⟩) (Lookup.readRowCost input.rows[e]) := by
    have hcursor : guardTapes input e base .cursor = Lookup.rowBits input.rows[e] ++
        LoopState.cursorBits input (e.val + 1) := by
      simpa only [guardTapes, Function.update_of_ne (by decide : Tape.cursor ≠ .counter),
        Lookup.rowBits] using ready.cursor.trans (LoopState.cursorBits_succ input e.val e.isLt)
    have htail : guardTapes input e base .tail = [] := by simp [guardTapes, ready.tail]
    have hreverse : guardTapes input e base .reverseIndex = [] := by
      simp [guardTapes, ready.reverseIndex]
    simpa only [normal, parsedTapes] using
      Lookup.readRowInTime Tape.cursor Tape.tail Tape.reverseIndex
        (by decide) (by decide) (by decide) Driver.Label.tailStart .tailLoop
        .reverseStart .reverseLoop .readPredicate .headCopyFirst (Driver.program q)
        (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
        (guardTapes input e base) input.rows[e] (LoopState.cursorBits input (e.val + 1))
        hcursor htail hreverse (oldFlag, false, none) oldRelation none
  have looked : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .headCopyFirst, normal input.rows[e].relation oldFlag, parsedTapes input e base⟩
      (some ⟨some (.compare .leftFirst), normal input.rows[e].relation oldFlag,
        workingTapes input e base⟩) (7 * N + 5) := by
    have htable : parsedTapes input e base (headPorts 0) = GenericGraphTables.tableBits input := by
      simpa [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes,
        LoopState.inputBits] using ready.original
    have hreverse : parsedTapes input e base (headPorts 1) =
        encodeWord (Lookup.headIndex input e).val := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, Lookup.headIndex]
    have hhead : parsedTapes input e base (headPorts 4) = [] := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes, ready.head]
    have hscratch : parsedTapes input e base (headPorts 5) = [] := by
      simp [headPorts, parsedTapes, Lookup.readRowTapes, guardTapes, ready.scratch]
    have run := Lookup.headLookupInTime headPorts headPorts_injective
      Driver.Label.headCopyFirst .headCopySecond .indexCopyFirst .indexCopySecond
      .headVertices .headDarts Driver.Label.headLookup (some (.compare .leftFirst))
      (Driver.program q) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      (fun _ => rfl) (parsedTapes input e base) input e htable hreverse hhead hscratch
      (normal input.rows[e].relation oldFlag).1 none
    simpa only [workingTapes, normal, N, LoopState.inputBits, Lookup.headTimePolynomial,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using run
  have hleft : workingTapes input e base .compareLeft = [] :=
    (workingTapes_other input e base .compareLeft (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareLeft
  have hright : workingTapes input e base .compareRight = [] :=
    (workingTapes_other input e base .compareRight (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.compareRight
  have hscratch : workingTapes input e base .scratch = [] :=
    (workingTapes_other input e base .scratch (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans ready.scratch
  let compared := CompareLoop.compareRowInTime Driver.Label.compare (Driver.rowEntry q)
    (Driver.program q) (fun _ => rfl) input e (workingTapes input e base)
    (workingTapes_tail input e base) (workingTapes_head input e base)
    hleft hright hscratch oldFlag
  let emitted := emitInTime input e (workingTapes input e base)
    (workingOperands input e base ready) hscratch
  let cleared := clearFieldsInTime (emittedTapes input e base) (CompareLoop.rowState input e).1
  have hedge : clearFieldsTapes (emittedTapes input e base) .edge = encodeWord e.val := by
    simp [clearFieldsTapes, emittedTapes, Emitter.resultTapes, workingTapes,
      Lookup.headLookupTapes, MachineLookup.tapes, headPorts, parsedTapes,
      Lookup.readRowTapes, guardTapes, ready.edge]
  let incremented := incrementInTime (clearFieldsTapes (emittedTapes input e base))
    (CompareLoop.rowState input e).1 e.val hedge
  let run₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guarded parsed
  let run₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ looked
  let run₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₂ compared
  let run₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₃ emitted
  let run₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₄ cleared
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₅ incremented
  refine {
    tapes := resultTapes input e base
    ready := result_ready input e base ready
    run := { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  }
  have hn : input.vertices ≤ N := GenericGraphTables.vertices_le_tableBits_length input
  have hm : input.darts ≤ N := GenericGraphTables.darts_le_tableBits_length input
  have hr : Lookup.readRowCost input.rows[e] ≤ 2 * N + 5 :=
    Lookup.readRowCost_table_le input e
  have ht : (emittedTapes input e base .tail).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.tail ≠ .reversed), workingTapes_tail,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].tail.isLt).trans hn
  have hv : (emittedTapes input e base .reverseIndex).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.reverseIndex ≠ .reversed), workingTapes_reverse,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[e].reverseIndex.isLt).trans hm
  have hh : (emittedTapes input e base .head).length ≤ N := by
    simp only [emittedTapes, Emitter.resultTapes,
      Function.update_of_ne (by decide : Tape.head ≠ .reversed), workingTapes_head,
      encodeWord_length]
    exact (Nat.succ_le_of_lt input.rows[input.rows[e].reverseIndex].tail.isLt).trans hn
  have budget := run.steps_le_m
  change run.steps ≤ (32 + 8 * (Enumeration.localCount q * (6 * (2 * 4104)))) * (N + 1)
  nlinarith

end BinPackingGames.Foundations.PCP.AlphabetTable.Body

namespace BinPackingGames.Foundations.PCP.AlphabetTable.LoopInitialization

open BinPackingGames.Foundations.Complexity
open RuntimeModel LoopState

theorem initialization_ready {q : Nat} (input : GenericGraphTables.Table q) :
    Ready input 0 (Initialization.loopTapes input) where
  le_darts := Nat.zero_le _
  original := rfl
  cursor := by
    change Initialization.rowsBits input = cursorBits input 0
    rw [cursorBits_zero]
    rfl
  vertices := rfl
  darts := rfl
  counter := by simp [Initialization.loopTapes]
  edge := rfl
  tail := rfl
  reverseIndex := rfl
  head := rfl
  scratch := rfl
  compareLeft := rfl
  compareRight := rfl
  output := rfl
  reversed := by
    change (Initialization.headerBits input).reverse = (prefixBits input 0).reverse
    rw [prefixBits_zero]
    rfl

end BinPackingGames.Foundations.PCP.AlphabetTable.LoopInitialization

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Loop

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def zeroGuardInTime (input : GenericGraphTables.Table q) (base : Tape → List Bool)
    (ready : LoopState.Ready input input.darts base)
    (relation : GenericGraphTables.RelationTable q) (flag : Bool) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some .guard, normal relation flag, base⟩
      (some ⟨some .reverseOutput, normal relation flag, base⟩) 1 := by
  have counterSelf : MachineUnaryCounter.counterTapes Tape.counter base 0 [] = base := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil,
      ← ready.counter_at_end, Function.update_eq_self]
  have run := MachineUnaryCounter.guardInTime_zero Tape.counter
    (Driver.Label.guard : Driver.Label q) .tailStart .reverseOutput
    (Driver.program q) (Driver.program_guard q) base [] (normal relation flag).1 none
  simpa only [counterSelf, normal] using run

structure LoopResult (input : GenericGraphTables.Table q) (e remaining : Nat)
    (base : Tape → List Bool) (oldRelation : GenericGraphTables.RelationTable q)
    (oldFlag : Bool) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some .guard, normal oldRelation oldFlag, base⟩
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (remaining * Body.bodyTime q (LoopState.inputBits input).length + 1)

def runRemaining (input : GenericGraphTables.Table q) :
    (remaining e : Nat) → e + remaining = input.darts →
    (base : Tape → List Bool) → LoopState.Ready input e base →
    (oldRelation : GenericGraphTables.RelationTable q) → (oldFlag : Bool) →
      LoopResult input e remaining base oldRelation oldFlag
  | 0, e, finished, base, ready, oldRelation, oldFlag => by
    have atEnd : e = input.darts := by omega
    subst e
    exact {
      tapes := base
      relation := oldRelation
      flag := oldFlag
      ready := ready
      run := by
        simpa only [Nat.zero_mul, Nat.zero_add] using
          zeroGuardInTime input base ready oldRelation oldFlag }
  | remaining + 1, e, finished, base, ready, oldRelation, oldFlag => by
    have beforeEnd : e < input.darts := by omega
    let edge : Fin input.darts := ⟨e, beforeEnd⟩
    let one := Body.rowStep input edge base ready oldRelation oldFlag
    let rest := runRemaining input remaining (e + 1) (by omega) one.tapes one.ready
      input.rows[edge].relation (CompareLoop.rowLoop input edge)
    let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ one.run rest.run
    refine {
      tapes := rest.tapes
      relation := rest.relation
      flag := rest.flag
      ready := rest.ready
      run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
    have budget := composed.steps_le_m
    simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using budget

attribute [local instance] OAI.BinPackingGames.Foundations.PCP.AlphabetTable.Loop.prefixRunSizeOf
structure PrefixResult (input : GenericGraphTables.Table q) where
  tapes : Tape → List Bool
  relation : GenericGraphTables.RelationTable q
  flag : Bool
  ready : LoopState.Ready input input.darts tapes
  run : StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    (initList (Driver.machine q) (GenericGraphTables.tableBits input))
    (some ⟨some .reverseOutput, normal relation flag, tapes⟩)
    (prefixTime q (LoopState.inputBits input).length)

def runPrefix (input : GenericGraphTables.Table q) : PrefixResult input := by
  let rows := runRemaining input input.darts 0 (by simp)
    (Initialization.loopTapes input) (LoopInitialization.initialization_ready input)
    (Vector.replicate (q * q) false) false
  let composed := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (Initialization.initializeInTime input) rows.run
  refine {
    tapes := rows.tapes
    relation := rows.relation
    flag := rows.flag
    ready := rows.ready
    run := { toEvalsTo := composed.toEvalsTo, steps_le_m := ?_ } }
  have budget := composed.steps_le_m
  change composed.steps ≤
    input.darts * Body.bodyTime q (LoopState.inputBits input).length + 1 +
      Initialization.time (LoopState.inputBits input).length at budget
  have rowCount : input.darts ≤ (LoopState.inputBits input).length :=
    GenericGraphTables.darts_le_tableBits_length input
  have rowBudget := Nat.mul_le_mul_right (Body.bodyTime q (LoopState.inputBits input).length)
    rowCount
  unfold prefixTime
  omega

end BinPackingGames.Foundations.PCP.AlphabetTable.Loop

namespace BinPackingGames.Foundations.PCP.AlphabetTable.Runtime

open Turing
open BinPackingGames.Foundations.Complexity
open RuntimeModel

noncomputable def tableOutputsInTime {q : Nat} (input : GenericGraphTables.Table q) :
    TM2OutputsInTime (Driver.machine q) (GenericGraphTables.tableBits input)
      (some (GraphTables.tableBits (Table.build input)))
      ((time q).eval (GenericGraphTables.tableBits input).length) := by
  let prefixRun := Loop.runPrefix input
  have hrun : StateTransition.EvalsToInTime (Driver.machine q).step
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some .reverseOutput, normal prefixRun.relation prefixRun.flag, prefixRun.tapes⟩)
      ((prefixPolynomial q).eval (GenericGraphTables.tableBits input).length) := by
    rw [prefixPolynomial_eval]
    exact prefixRun.run
  exact Finish.finishAfterPolynomialPrefix q (GenericGraphTables.tableBits input)
    prefixRun.tapes (GraphTables.tableBits (Table.build input))
    (normal prefixRun.relation prefixRun.flag) (prefixPolynomial q) hrun
    prefixRun.ready.reversed_at_end prefixRun.ready.output

noncomputable def tablePolynomialTime (q : Nat) :
    TM2ComputableInPolyTime (GenericGraphTables.tableBits (q := q))
      GraphTables.tableBits (Table.build (q := q)) where
  tm := Driver.machine q
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time q
  outputsFun input := by
    change TM2OutputsInTime (Driver.machine q) ((GenericGraphTables.tableBits input).map id)
      (some ((GraphTables.tableBits (Table.build input)).map id)) _
    have input_eq : @List.map ((Driver.machine q).Γ (Driver.machine q).k₀)
        ((Driver.machine q).Γ (Driver.machine q).k₀) id (GenericGraphTables.tableBits input) =
          GenericGraphTables.tableBits input := List.map_id _
    have output_eq : @List.map ((Driver.machine q).Γ (Driver.machine q).k₁)
        ((Driver.machine q).Γ (Driver.machine q).k₁) id (GraphTables.tableBits (Table.build input)) =
          GraphTables.tableBits (Table.build input) := List.map_id _
    simpa only [Equiv.refl, input_eq, output_eq] using tableOutputsInTime input

end BinPackingGames.Foundations.PCP.AlphabetTable.Runtime

namespace BinPackingGames.Foundations.PCP.RoundComputation

open Turing
open BinPackingGames.Foundations.Complexity

noncomputable def tablePolynomialTimeOfCertificates (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) (powering : PoweringCertificate) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) := by
  change TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
    (fun table => AlphabetTable.Table.build (RoundTables.powered H table))
  exact MachineSequential.composeBits
    (poweredPolynomialTimeOfCertificates H preprocessing powering)
    (AlphabetTable.Runtime.tablePolynomialTime RoundTables.alphabet)

noncomputable def tablePolynomialTime (H : RoundTables.BaseTable)
    (preprocessing : PreprocessingCertificate H) :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build H) :=
  tablePolynomialTimeOfCertificates H preprocessing
    (PoweringMachineRuntime.computableInPolyTime PreprocessingTables.degree
      RoundTables.walkParameter)

end BinPackingGames.Foundations.PCP.RoundComputation

namespace BinPackingCompleteness.PreprocessingMachine

open Turing BinPackingGames.Foundations
open Complexity PCP Target

def round :
    TM2ComputableInPolyTime GraphTables.tableBits GraphTables.tableBits
      (RoundTables.build PCPSource.baseTable) :=
  RoundComputation.tablePolynomialTime PCPSource.baseTable preprocessing

def computableInPolyTime :
    TM2ComputableInPolyTime formulaBits formulaBits PCPSource.rawFormula :=
  MachineTableIteration.gapMapCertificate PCPSource.baseTable round

end BinPackingCompleteness.PreprocessingMachine

namespace BinPackingCompleteness.PCPSourceMachine

open Turing BinPackingGames.Foundations Complexity Target

def normalizedComputation :
    TM2ComputableInPolyTime formulaBits formulaBits PCPSource.normalizedFormula := by
  change TM2ComputableInPolyTime formulaBits formulaBits
    (fun formula => Normalization.normalize (PCPSource.rawFormula formula))
  exact MachineSequential.composeBits PreprocessingMachine.computableInPolyTime
    NormalizationMachine.computableInPolyTime

end BinPackingCompleteness.PCPSourceMachine

namespace BinPackingCompleteness.PCPSourceHardness

open Turing BinPackingGames.Foundations Complexity Target

def computation {language : List Bool → Prop}
    (source : CookLevin.PolynomialThreeSATReduction language) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits (formula source) := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => PCPSource.normalizedFormula (source.reduce input))
  exact MachineSequential.composeBits source.computation PCPSourceMachine.normalizedComputation

end BinPackingCompleteness.PCPSourceHardness

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

def fillBody (s : State) : List Bool :=
  fillHeader s ++ rawInstanceBits s.items ++ fixedBits (newFixed s)

end BinPackingGap.SearchUpdateMachine

end OAI
end


