-- Prove2me | Definitions.Def_OAIQ087A014
-- name    : OAIQ087A014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:25:22.070785+00:00
-- url     : https://prove2.me/theorems/491ada94-d116-4728-b806-fdf1d7565473
-- title:
--   Definitions bundle OAIQ087A014 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 710 declarations of OpenAI's Lean: 351 definitions, 4 inductive types or structures, 4 instances and 351 theorems. The definitions and types are `OAI.MaxCutGames.BinaryInputReduction.computation`, `OAI.MaxCutGames.BinaryRenameMachine.computableInPolyTime`, `OAI.MaxCutGames.BinaryRenameMachine.outputsInTime`, `OAI.MaxCutGames.BinaryRenameMachine.tokenComputation`, `OAI.MaxCutGames.BinaryTotalInputMachine.cfg`, `OAI.MaxCutGames.BinaryTotalInputMachine.computableInPolyTime`, `OAI.MaxCutGames.BinaryTotalInputMachine.instruction`, `OAI.MaxCutGames.BinaryTotalInputMachine.machine`, `OAI.MaxCutGames.BinaryTotalInputMachine.outputsInTime`, `OAI.MaxCutGames.BinaryTotalInputMachine.rejectedWord`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFPattern.labelEquiv`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFPattern.labelIndex`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFPattern.patternRelationIndex`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFPattern.relationAddress`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFPattern.tableGraph`, `OAI.MaxCutGames.Foundations.Complexity.MachineAlphabetTransport.executionInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineAlphabetTransport.successfulExecutionInTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCeilingPower.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.Alphabet`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.BoolAlphabet`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.Label`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.RegisterAmbient`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.State`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.Tape`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.affineCoefficient`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.affineDestination`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.affineExit`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.affineSource`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.affineStatement`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.boolOuterStatement`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.boolView`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.boolWord`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.boundaryTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.caller`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.clearRegister`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.cycleTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.cycleWords`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.drainStatement`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.extraFrame`, `OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.familyTapes` and 315 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Games_FinalCNFPattern`, `MaxCut_Machines_AlphabetGraph`, `MaxCut_Machines_AlphabetReduction`, `MaxCut_Machines_AlphabetRetraction`, `MaxCut_Machines_EmitRows`, `MaxCut_Machines_Input`, `MaxCut_Machines_Lookup`, `MaxCut_Machines_MachineBinaryInputReduction`, `MaxCut_Machines_MachineBinaryNameCompare`, `MaxCut_Machines_MachineBinaryParsing`, `MaxCut_Machines_MachineBinaryRenameLoop`, `MaxCut_Machines_MachineBinaryRenameWords`, `MaxCut_Machines_MachineClone100`, `MaxCut_Machines_MachineCloudCount`, `MaxCut_Machines_MachineCloudPrefix`, `MaxCut_Machines_MachineExpanderFamilyAffine`, `MaxCut_Machines_MachineExpanderFamilyCycle`, `MaxCut_Machines_MachineExpanderRowFrames`, `MaxCut_Machines_MachineExpanderTableProgram`, `MaxCut_Machines_MachineExpanderTableRows`, `MaxCut_Machines_MachineFixedDivMod`, `MaxCut_Machines_MachineLookupCore`, `MaxCut_Machines_MachinePaddedExpanderFamilyBounds`, `MaxCut_Machines_MachineSequential`, `MaxCut_Machines_MachineSubroutine`, `MaxCut_Machines_Relations`, `MaxCut_Machines_Runtime`, `MaxCut_Machines_RuntimeModel`, `MaxCut_Machines_RuntimeSpace`, `MaxCut_PCP_ContextClear`, `MaxCut_PCP_ContextPrepare`, `MaxCut_PCP_DescriptorEmission`, `MaxCut_PCP_ExpanderFamily`, `MaxCut_PCP_ExpanderRowControl`, `MaxCut_PCP_ExpanderTableEnumeration`, `MaxCut_PCP_FinalBooleanVerifier`, `MaxCut_PCP_Game`, `MaxCut_PCP_Gap`, `MaxCut_PCP_GraphGap`, `MaxCut_PCP_HeaderAccumulate`, `MaxCut_PCP_HeaderCounts`, `MaxCut_PCP_InitialGraph`, `MaxCut_PCP_LocalEquation`, `MaxCut_PCP_LoopOrder`, `MaxCut_PCP_Occurrences`, `MaxCut_PCP_PortTables`, `MaxCut_PCP_PoweringOpinionTables`, `MaxCut_PCP_PoweringTableSemantics`, `MaxCut_PCP_PreprocessingRegularSoundness`, `MaxCut_PCP_PreprocessingRegularTables`, `MaxCut_PCP_ProfileBridge`, `MaxCut_PCP_RawInitialTables`, `MaxCut_PCP_RoundGap`, `MaxCut_PCP_TupleBody`.
--
--   **Imports.** It imports the published bundle `Def_OptimalMaxCut`; the bundles `OAIQ087A007` and `OAIQ087A008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A021`, `OAIQ087A022`, `OAIQ087A023`, `OAIQ087A024`, `OAIQ087A025`, `OAIQ087A026` and `OAIQ087A027`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OptimalMaxCut
import Definitions.Def_OAIQ087A007
import Definitions.Def_OAIQ087A008

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Runtime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Stack-length bounds derived from actual machine transitions. A finite program
has a maximum number of pushes in any one statement. Iterating its transitions
therefore bounds output length by input length plus that constant times elapsed
steps. This proves a consequence of a runtime certificate, not its converse.
-/

/-! Exact embedding of a finite-stack program into disjoint stacks and labels.
An original halt can either halt or enter an explicit continuation label.
The simulation preserves all extra stacks and the second state component. -/

/-!
Execution transport and polynomial budget arithmetic for genuine TM2 sequential
composition. These lemmas preserve actual transition witnesses. The four-phase
lemma requires all phases to be executions of the same combined program; it is
not a replacement for constructing that program and proving its tape handoffs.
-/

/-!
# Certified reversal and relabeling between finite alphabets

The actual TM2 machine transfers a list over a finite alphabet `α` to a second
stack over `β`, reverses its order, and applies a fixed map `f : α → β` to each
symbol. The trace has exactly `input.length + 1` transitions. An explicit
fallback symbol makes the push expression total, including the unused branch
where the internal register is empty.

This primitive supports machine composition when intermediate stack alphabets
differ. It does not yet implement the Unique Games reduction.
-/

namespace MaxCutGames.Reduction.MachineTransfer

open Turing

variable {α β : Type} [Fintype α] [Fintype β]

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

/-- A timed execution witness suitable for composing this bridge with other
phases of the same actual transition system. -/
def transferAtInTime (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩)
      ((base src).length + 1) where
  steps := (base src).length + 1
  evals_in_steps := transferAt_fromTapes src dst distinct f fallback loopLabel exit
    program atLoop base ambient register
  steps_le_m := Nat.le_refl _

end MaxCutGames.Reduction.MachineTransfer

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSequential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineSequential

open Turing

def firstTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (first.Γ first.k₁)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (firstConfiguration first second (haltList first word))
      (some (temporaryConfiguration first second (word.reverse.map relabel)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inl first.k₁ : Tape first second) (.inr (.inr ())) (by intro h; cases h)
    relabel fallback (bridgeLabel first second false)
    (some (bridgeLabel first second true)) (program first second relabel fallback) rfl
    (firstConfiguration first second (haltList first word)).stk
    (first.initialState, second.initialState) none
  have inputTape : (firstConfiguration first second (haltList first word)).stk (.inl first.k₁) =
      word := by simp [firstConfiguration, MachineControl.configuration,
        MachineEmbedding.configuration, MachineEmbedding.tapes, haltList]
  have outputTape :
      (firstConfiguration first second (haltList first word)).stk (.inr (.inr ())) = [] := rfl
  rw [inputTape, outputTape, List.append_nil, firstTransfer_tapes] at run
  exact run

def secondTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (second.Γ second.k₀)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (temporaryConfiguration first second word)
      (some (secondConfiguration first second (initList second word.reverse)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inr (.inr ()) : Tape first second) (.inr (.inl second.k₀)) (by intro h; cases h)
    id fallback (bridgeLabel first second true) (some (.inr (.inr second.main)))
    (program first second relabel fallback) rfl (temporaryTapes first second word)
    (first.initialState, second.initialState) none
  simp only [temporaryTapes, List.map_id, List.append_nil] at run
  rw [secondTransfer_tapes] at run
  exact run

/-- An execution of each component yields an actual execution of the combined
machine. The two transfer loops add exactly twice the intermediate length plus two. -/
def execute (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (input : List (first.Γ first.k₀)) (middle : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₁)) (firstBudget secondBudget : Nat)
    (runFirst : TM2OutputsInTime first input (some middle) firstBudget)
    (runSecond : TM2OutputsInTime second (middle.map relabel) (some output) secondBudget) :
    TM2OutputsInTime (machine first second relabel fallback) input (some output)
      (firstBudget + 2 * (middle.length + 1) + secondBudget) := by
  let start := MachineComposition.liftExecutionInTime first.step
    (machine first second relabel fallback).step (firstConfiguration first second)
    (firstStep first second relabel fallback) runFirst
  let bridge₁ := firstTransfer first second relabel fallback middle
  have bridge₂ := secondTransfer first second relabel fallback (middle.reverse.map relabel)
  have reversal : (middle.reverse.map relabel).reverse = middle.map relabel := by
    simp only [List.map_reverse, List.reverse_reverse]
  rw [reversal] at bridge₂
  simp only [List.length_map, List.length_reverse] at bridge₂
  let finish := MachineComposition.liftExecutionInTime second.step
    (machine first second relabel fallback).step (secondConfiguration first second)
    (secondStep first second relabel fallback) runSecond
  let phase₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start bridge₁
  let phase₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂ bridge₂
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂₃ finish
  rw [firstConfiguration_init, secondConfiguration_halt] at full
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by have h := full.steps_le_m; omega
  }

/-- General sequential composition with an explicit symbol of the intermediate
alphabet to totalize the bridge's unused empty-register expression. Its time
polynomial uses the transition-derived output-length bound of the first machine. -/
noncomputable def compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) := by
  let relabel : first.tm.Γ first.tm.k₁ → second.tm.Γ second.tm.k₀ :=
    fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol)
  let defaultSymbol := second.inputAlphabet.symm fallback
  let intermediate : Polynomial Nat := Polynomial.X +
    Polynomial.C (Runtime.programPushBound first.tm) * first.time
  refine {
    tm := machine first.tm second.tm relabel defaultSymbol
    inputAlphabet := first.inputAlphabet
    outputAlphabet := second.outputAlphabet
    time := MachineComposition.compositionPolynomial first.time second.time intermediate
    outputsFun := ?_
  }
  intro a
  let input := (ea a).map first.inputAlphabet.invFun
  let middle := (eb (f a)).map first.outputAlphabet.invFun
  let output := (ec (g (f a))).map second.outputAlphabet.invFun
  have handoff : middle.map relabel = (eb (f a)).map second.inputAlphabet.invFun := by
    dsimp only [middle, relabel]
    simp only [List.map_map]
    apply List.map_congr_left
    intro symbol _
    exact congrArg second.inputAlphabet.symm (first.outputAlphabet.apply_symm_apply symbol)
  have runSecond : TM2OutputsInTime second.tm (middle.map relabel) (some output)
      (second.time.eval (eb (f a)).length) := by
    rw [handoff]
    exact second.outputsFun (f a)
  have full := execute first.tm second.tm relabel defaultSymbol input middle output
    (first.time.eval (ea a).length) (second.time.eval (eb (f a)).length)
    (first.outputsFun a) runSecond
  have intermediateBound : (eb (f a)).length ≤ intermediate.eval (ea a).length :=
    Runtime.encodedOutputLength first a
  have totalBound := MachineComposition.compositionBudget_le first.time second.time
    intermediate (ea a).length (eb (f a)).length intermediateBound
  have middleLength : middle.length = (eb (f a)).length := by simp only [middle, List.length_map]
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans full.steps_le_m
      simpa only [middleLength] using totalBound
  }

noncomputable def composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) :=
  compose first second false

end MaxCutGames.Foundations.Complexity.MachineSequential

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate tape-space bounds derived from actual successful machine
prefixes, and their use in the separately checked physical finalizer. -/

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

namespace MaxCutGames.Foundations.Complexity.MachineFiniteAlphabet

open Turing

/-- Preservation for the machine actually stored in the polynomial-time
composition certificate, with its actual relabeling bridge. -/
theorem compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.compose first second fallback).tm := by
  exact sequential_machine first.tm second.tm
    (fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol))
    (second.inputAlphabet.symm fallback) hfirst hsecond

theorem composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g)
    (hfirst : FiniteAlphabet first.tm) (hsecond : FiniteAlphabet second.tm) :
    FiniteAlphabet (MachineSequential.composeBits first second).tm :=
  compose first second false hfirst hsecond

end MaxCutGames.Foundations.Complexity.MachineFiniteAlphabet

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLookupCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite control for destructive unary-indexed table lookup. The guard decreases
the index even when the table is exhausted. Selection tests for an empty table
before writing the destination. All tests inspect just one finite head register.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

/-- Six fixed labels and a single optional-bit register, independent of input. -/
def program (index source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard index .skip .select
  | .skip => discard source .skip .guard
  | .select => select source destination .copy .rejected
  | .copy => Hastad.SourceMachine.fieldLoop source destination .copy (some .accepted)
  | .accepted => .halt
  | .rejected => .halt

end MaxCutGames.Foundations.Complexity.MachineLookup

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/

/-!
Execution of the destructive field-discard loop in an arbitrary ambient TM2
program. The scanner consumes a unary payload and its delimiter, preserves the
ambient state and other tapes, and clears its head register on return. At EOF it
returns immediately, leaving the tapes unchanged.
-/

/-!
Actual traces for the fixed unary lookup machine. Successful lookup preserves
an arbitrary unread table suffix. Rejection relative to a list's end is stated
only for its complete, unframed encoding, so no hidden endpoint is assumed.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Occurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Executable radix numbering of padded global long-code tables and an ordered
equation occurrence list. The code enumerates random tapes, not distinct
equations: coinciding equations and repeated variable occurrences are retained.
-/

namespace MaxCutGames.Foundations.Hastad.SourceOccurrences

open MaxCutGames.Reduction.CloneGap
open scoped BigOperators

open SourceContexts
open MaxCutGames.Reduction.FiniteNoise

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
    MaxCutGames.Reduction.SourceEncoding.Input :=
  ⟨nBits F u, sourceList F u D, sourceList_ne_nil F u D hD⟩

end MaxCutGames.Foundations.Hastad.SourceOccurrences

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Game
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceHonest

open MaxCutGames.Reduction.CloneGap
open MaxCutGames.Reduction.FiniteNoise
open scoped BigOperators

open SourceContexts
open SourceOccurrences

/-- A single assignment to the globally tagged padded tables. It is defined
from the input assignment alone, before any incidence or test is sampled. -/
def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun c => honestJ F c assignment)

/-- The same global proof in the construction's explicit radix numbering. -/
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

end MaxCutGames.Foundations.Hastad.SourceHonest

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubroutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace MaxCutGames.Foundations.Complexity.MachinePreservingLookup

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def program (tape : Fin 5 → K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (tape 0) (tape 4) id false .copyFirst (some .copySecond)
  | .copySecond => MachineCopy.forkLoop (tape 4) (tape 0) (tape 2) false .copySecond (some (.lookup .guard))
  | .lookup l => MachineSubroutine.statement Label.lookup none
      (MachineLookup.program (tape 1) (tape 2) (tape 3) l)

end MaxCutGames.Foundations.Complexity.MachinePreservingLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

/-!
Counted loops in one actual TM2 program. A unary guard is executed once before
each caller body and once more at zero. The caller supplies only individual
body traces, each returning to the guard with the same counter remainder.

Schedules are indexed by the remaining count: body `r` takes ambient state
`r + 1` to ambient state `r`. Consequently the run starts at index `n` and
ends at index zero. Bodies may change the ambient state and unprotected tapes.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ProfileBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceProfileBridge

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

end MaxCutGames.Foundations.Hastad.SourceProfileBridge

namespace MaxCutGames.Foundations.Hastad.SourceSignaturePrepare

open Turing
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge
open MaxCutGames.Foundations.Complexity

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

end MaxCutGames.Foundations.Hastad.SourceSignaturePrepare

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextPrepare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceContextPrepare

open Turing MaxCutGames.Foundations.Complexity
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

end MaxCutGames.Foundations.Hastad.SourceContextPrepare

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_LocalEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceLocalEquation

open Target SourceContexts SourceOccurrences SourceLocalSignature
open MaxCutGames.Reduction.CloneGap
open MaxCutGames.Reduction.FiniteNoise

abbrev LocalInput (u D : ℕ) := Signature u × SourceTape.TestTape (I u) (J u) D

end MaxCutGames.Foundations.Hastad.SourceLocalEquation

/-! The actual global addresses use three input-dependent base registers.
Every local query contributes only a fixed finite selector and fixed offset,
so a finite control table can select a base and emit its unary offset. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_DescriptorEmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceTestEmit

open Turing
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open MaxCutGames.Reduction.CloneGap
open Complexity

abbrev State (u D : ℕ) := LocalInput u D × Option Bool

end MaxCutGames.Foundations.Hastad.SourceTestEmit

namespace MaxCutGames.Foundations.Hastad.SourceTestAppend

open Turing Complexity
open Target SourceContexts SourceOccurrences SourceLocalSignature SourceLocalEquation
open SourceTestEmit

abbrev State (u D : Nat) := SourceTestEmit.State u D

end MaxCutGames.Foundations.Hastad.SourceTestAppend

/-! An actual fixed finite traversal of all query/noise tapes. The finite
control contains one branch for each prescribed tape. The input-dependent
signature and the three address bases remain in registers throughout. -/

namespace MaxCutGames.Foundations.Hastad.SourceQueryLoop

open Turing Complexity Target SourceContexts SourceOccurrences
open SourceLocalSignature SourceLocalEquation

abbrev Query (u D : Nat) := SourceTape.TestTape (I u) (J u) D
abbrev State (u D : Nat) := SourceTestAppend.State u D

end MaxCutGames.Foundations.Hastad.SourceQueryLoop

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceRuntimeModel

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

end MaxCutGames.Foundations.Hastad.SourceRuntimeModel

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_LoopOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

@[simp] theorem final_accumulator (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.extra accumulator) =
      ((tupleOrder m u).flatMap bits).reverse ++ base (.extra accumulator) := by
  simp [finalConfiguration, configuration, allBits]

end MaxCutGames.Foundations.Hastad.SourceOdometerSchedule

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextClear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceContextClear

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

end MaxCutGames.Foundations.Hastad.SourceContextClear

namespace MaxCutGames.Foundations.Hastad.SourceTupleTape

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

end MaxCutGames.Foundations.Hastad.SourceTupleTape

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HeaderCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorModel

open Turing Complexity SourceRuntimeModel

abbrev State (u D : Nat) := SourceRuntimeModel.State u D

abbrev ControlAmbient (u D : Nat) := (Unit × Unit) × ArithmeticMetadata u D

/-- Expose the existing arithmetic head register to the odometer and final
cleanup. This is a static finite-state equivalence, with no machine steps. -/
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

end MaxCutGames.Foundations.Hastad.SourceGeneratorModel

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_HeaderAccumulate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceStartup

open Turing Complexity SourceRuntimeModel SourceGeneratorModel
open MachineComposition

noncomputable section

variable {u D : Nat}

attribute [local instance] OAI.MaxCutGames.Foundations.Hastad.SourceStartup.instDecidableEqExtra
@[simp] theorem ready_field (F : Target.Formula) (j : Fin u) (s : Fin 6) :
    readyTapes (D := D) F (.field j s) = [] := initialized_field F j s

@[simp] theorem ready_sharedWork (F : Target.Formula) :
    readyTapes (u := u) (D := D) F .work = [] := by
  simp [readyTapes, initializedTapes]

end

end MaxCutGames.Foundations.Hastad.SourceStartup

/-! Actual fixed-coefficient affine address construction. A finite literal phase
loads the coefficient, the checked width-two Horner machine reads coefficient
and preserved offset with the rank as its radix, then the literal field is
actually consumed. All operands and work stacks are restored. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_TupleBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One actual clause-tuple body. Its fixed finite control loads the context,
computes the shared right address base, traverses every selected-slot tuple and
query tape in their declared encoding order, and physically clears its work.
-/

namespace MaxCutGames.Foundations.Hastad.SourceTupleBody

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature
open SourceRuntimeModel SourceTupleTape

abbrev SlotCount (u : Nat) := (slotContextEncoding u).size
abbrev Query (u D : Nat) := SourceQueryLoop.Query u D

variable {u D : Nat} {Extra : Type}

def selected (index : Fin (SlotCount u)) : SlotContext u :=
  (slotContextEncoding u).code.symm index

variable [DecidableEq Extra]

/-- Only the chosen-slot/query registers change; the computed context profile
and original signature remain available across all local traversals. -/
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

end MaxCutGames.Foundations.Hastad.SourceTupleBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Gap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An executable finite-noise denominator for a positive rational target error.
Using the stored rational denominator avoids rounding, searches, and choice.
-/

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorProgram

open Turing Complexity SourceGeneratorModel

noncomputable section

abbrev Ambient (u D : Nat) := SourceGeneratorModel.ControlAmbient u D
abbrev State (u D : Nat) := Ambient u D × Option Bool

local instance instDecidableEqExtra_rd3fd41_1 (u D : Nat) : DecidableEq (Extra u D) := Classical.decEq _
def sourceStateEquiv (u D : Nat) : SourceRuntimeModel.State u D × Unit ≃ State u D where
  toFun x := (controlStateEquiv u D).symm x.1
  invFun x := (controlStateEquiv u D x, ())
  left_inv x := by cases x with | mk x y => cases y; simp
  right_inv x := by simp

end

end MaxCutGames.Foundations.Hastad.SourceGeneratorProgram

/-! Uniform polynomial bounds for the actual tuple-body phase budgets.
The budget being bounded is the one used by the checked machine traces. -/

namespace MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

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
    (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse

@[simp] theorem traversalOutput_accumulator (F : Target.Formula) (hD : 0 < D) :
    traversalOutput F hD (accumulatorTape u D) =
      (MaxCutGames.Reduction.SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  simp [traversalOutput]

end

end MaxCutGames.Foundations.Hastad.SourceGeneratorTraversal

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_InitialGraph
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The initial finite constraint graph of an arbitrary concrete 3CNF formula.
Clause and variable vertices use one eight-element alphabet. Variable labels
are the canonical triples `(bit, false, false)`; clause labels are arbitrary
triples. Every incidence has two directed darts, including repeated names.
A tautological dummy loop keeps the graph nonempty for empty formulas.

Name compaction precedes the public construction. The resulting vertex count
is at most `4*m+1`, and the dart count is exactly `6*m+1`. Unsatisfiability gives
an inverse-size gap, not a constant gap. No PCP theorem is assumed or claimed.
-/

namespace MaxCutGames.Foundations.PCP.InitialGraph

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

end MaxCutGames.Foundations.PCP.InitialGraph

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PortTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable regular constraint tables on the fixed 64-label alphabet

Every pair `(vertex,port)` has one stored reverse index and one complete
4096-bit relation. Flat row `port + ports * vertex` has its tail implicitly
fixed by that pair. Rotation uses the stored vector lookup, followed by the
inverse row-index bijection. Loops and repeated directed occurrences remain
distinct rows.

Serialization uses the existing `GraphTables` codec: header `[vertices,darts]`
with `darts=vertices*ports`, then tail/reverse/4096 bit words per row.
-/

/-! A concrete constant-query proximity tester for a finite relation.

The proof oracle is a Boolean function on the Boolean functions on the finite
set of legal assignments. The tests are BLR linearity, self-corrected AND,
self-corrected unit, and comparison with a queried input coordinate.
The oracle's size depends exponentially on the number of legal assignments;
this is a fixed-relation construction, not a polynomial-size tester for an
arbitrary input formula. All tests below are explicit finite expectations.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.AssignmentTester

open MaxCutGames.Foundations.Hastad
open scoped BigOperators
open Finset

variable {A : Type*} [Fintype A] [DecidableEq A]

def cubeAnd (f g : Cube A) : Cube A := fun a => f a && g a

variable {K : Type*} [Fintype K] [Nonempty K]

/-- The actual six oracle addresses for each test. Unused slots repeat an
address already queried, so every event has the same fixed six-slot format. -/
def eventQueries (label : A → K → Bool) (kind : Fin 4) (k : K)
    (f g r₀ r₁ r₂ : Cube A) (slot : Fin 6) : K ⊕ Cube A :=
  if kind = 0 then
    if slot = 0 then .inr f else if slot = 1 then .inr g else .inr (cubeXor f g)
  else if kind = 1 then
    if slot = 0 then .inr r₀ else
    if slot = 1 then .inr (cubeXor r₀ (cubeAnd f g)) else
    if slot = 2 then .inr r₁ else
    if slot = 3 then .inr (cubeXor r₁ f) else
    if slot = 4 then .inr r₂ else .inr (cubeXor r₂ g)
  else if kind = 2 then
    if slot = 0 then .inr r₀ else .inr (cubeXor r₀ (fun _ => true))
  else
    if slot = 0 then .inl k else
    if slot = 1 then .inr r₀ else .inr (cubeXor r₀ (fun a => label a k))

end MaxCutGames.Foundations.PCP.AssignmentTester
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A concrete finite family from the Cayley base

The initial graph has one vertex and the fixed number of loop ports. Each
subsequent graph is the actual square-and-zigzag construction. Consequently
the vertex sizes are exact powers of one fixed integer, including size one.
The finite base is selected from the proved existence theorem.
-/

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

/-- The actual square/zigzag graph, expressed in the table's integer coordinates. -/
def stepGraph {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    PortGraph (Fin (v * ((d * d) * (d * d)))) (Fin (d * d)) :=
  GraphTransport.reindex
    (ZigzagGraphs.zigzag (ZigzagGraphs.square (graph G))
      (GraphTransport.reindex (graph H) (rowIndex (d * d) (d * d)).symm (Equiv.refl _)))
    (vertexIndex v (d * d)) (rowIndex d d)

/-- Materialize every row of the next table in the declared order. -/
def step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    Table (v * ((d * d) * (d * d))) (d * d) := ofGraph (stepGraph G H)

/-- A row uses exactly the displayed four lookups in already stored tables. -/
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

/-- A bottom-up vector of rotation rows. The recursive result is passed once
to `step`, whose row formula reads only that already materialized table. -/
def family {d : Nat} (H : Table ((d * d) * (d * d)) d) :
    (n : Nat) → Table (vertexCount (d * d) n) (d * d)
  | 0 => initial d
  | n + 1 => step (family H n) H

end MaxCutGames.Foundations.PCP.ExpanderTables

namespace MaxCutGames.Foundations.PCP.PreprocessingLevels

@[simp] theorem boundedLevel_zero : boundedLevel 0 = 0 := rfl

@[simp] theorem paddedSize_zero : paddedSize 0 = 1 := rfl

end MaxCutGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_GraphGap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Foundations.PCP.ConstraintGraph

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

/-- Explicit changes of vertex, dart, and label coordinates. -/
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

end MaxCutGames.Foundations.PCP.ConstraintGraph

end

namespace MaxCutGames.Foundations.PCP.PreprocessingOverlayTables

open PoweringWalks

/-- Add the expander's stored ports; every new constraint always accepts. -/
def overlay {n d e : Nat} (G : PortTables.Table n d) (H : ExpanderTables.Table n e) :
    PortTables.Table n (d + e) :=
  materialize (Overlay.constraintGraph (PortTables.baseGraph G) (ExpanderTables.graph H))
    (overlayPorts d e)

@[simp] theorem overlay_accepts_old {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (overlay G H) (v, overlayPorts d e (Sum.inl i)) a b =
      PortTables.accepts G (v, i) a b := by
  simp only [overlay, accepts_materialize, Equiv.symm_apply_apply]
  rfl

@[simp] theorem overlay_accepts_expander {n d e : Nat} (G : PortTables.Table n d)
    (H : ExpanderTables.Table n e) (v : Fin n) (i : Fin e) (a b : PortTables.Label) :
    PortTables.accepts (overlay G H) (v, overlayPorts d e (Sum.inr i)) a b = true := by
  simp only [overlay, accepts_materialize, Equiv.symm_apply_apply]
  rfl

def lazy {n d : Nat} (G : PortTables.Table n d) : PortTables.Table n (2 * d) :=
  materialize (LazyConstraint.constraintGraph (PortTables.baseGraph G)) (lazyPorts d)

@[simp] theorem lazy_accepts_false {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (lazy G) (v, lazyPorts d (false, i)) a b = true := by
  simp only [lazy, accepts_materialize, Equiv.symm_apply_apply]
  rfl

@[simp] theorem lazy_accepts_true {n d : Nat} (G : PortTables.Table n d)
    (v : Fin n) (i : Fin d) (a b : PortTables.Label) :
    PortTables.accepts (lazy G) (v, lazyPorts d (true, i)) a b =
      PortTables.accepts G (v, i) a b := by
  simp only [lazy, accepts_materialize, Equiv.symm_apply_apply]
  rfl

end MaxCutGames.Foundations.PCP.PreprocessingOverlayTables

/-!
Actual finite counting for rounding copied dart labels. Minority color classes
are small enough for the cloud's directed-cut expansion. Their boundary darts
inject into all label disagreements. A separate endpoint charge counts at
most two affected original darts per changed copied label.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable degree replacement on the actual finite constraint rows

Vertices are numbered by first listing the original darts, then the dummy
darts in original-vertex order. Each local cloud uses its explicit filtered
dart list. Internal ports carry equality; the final port retains the original
constraint, or an always-accepting loop at a dummy dart. The constructor is
total, including inputs with no darts. The fixed base expander is supplied
once; every input-dependent operation is an explicit finite calculation.
-/

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingTables

open PoweringWalks PortTables

variable {n m d : Nat}

/-- A computable extension uses label zero on every dummy vertex. -/
def extendLabeling (h : n ≤ m) (labeling : Fin n → Label) : Fin m → Label :=
  fun v => Sum.elim labeling (fun _ => 0) ((vertexEquiv h).symm v)

@[simp] theorem extendLabeling_old (h : n ≤ m) (labeling : Fin n → Label) (v : Fin n) :
    extendLabeling h labeling (v.castLE h) = labeling v := by
  simp only [extendLabeling, vertexEquiv_symm_old, Sum.elim_inl]

end MaxCutGames.Foundations.PCP.PreprocessingPaddingTables

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Soundness of the executable regularization tables

The fixed input base table is required only to have its proved spectral
certificate. Every positive cloud uses the actual recursively generated table
at its computed size. Its spectral certificate gives the precise cut bound
used by majority rounding. Empty clouds are handled by their zero cardinality.
Thus neither expansion nor the desired count comparison is an input premise.
-/

/-!
Spectral certificates for the actual materialized preprocessing tables.
Exact rotation identities transport the checked semantic overlay and lazy
estimates to the stored tables. No spectral premise is imposed on the
original constraint table in the overlay theorem.
-/

/-! Soundness and expansion of the actual executable preprocessing tables.
The fixed base-table spectral certificate is supplied by the proved expander
existence theorem; no output expansion or output gap is assumed. -/

/-! Full-radius local opinions use a common alphabet indexed by bounded
port addresses. Every opinion is decoded through a fixed address selector;
arbitrary alphabet symbols need not agree on colliding addresses. -/

namespace MaxCutGames.Foundations.PCP.PoweringLabels

open PoweringWalks
open scoped BigOperators

variable {V D A : Type*}

theorem wordToBall_surjective (G : PortGraph V D) (t : Nat) (v : V) :
    Function.Surjective (wordToBall G t v) := by
  intro u
  obtain ⟨n, hn, p, hp⟩ := u.property
  refine ⟨⟨⟨n, Nat.lt_succ_of_le hn⟩, p⟩, ?_⟩
  exact Subtype.ext hp

/-- A concrete complete address list supplies a computational selector. Its
length depends on the degree and radius, not on the ambient vertex count. -/
def listSelector [DecidableEq V] (G : PortGraph V D) (t : Nat) (v : V)
    (addresses : List (PortWords D t)) (complete : ∀ w, w ∈ addresses) :
    AddressSelector G t v where
  address u := (scanWitness (fun w => (wordToBall G t v w).val = u.val) addresses (by
    obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
    exact ⟨w, complete w, congrArg Subtype.val hw⟩)).val
  correct u := Subtype.ext (scanWitness
    (fun w => (wordToBall G t v w).val = u.val) addresses (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t v u
      exact ⟨w, complete w, congrArg Subtype.val hw⟩)).property

end MaxCutGames.Foundations.PCP.PoweringLabels

/-!
# Executable bounded port-address enumeration

For a port alphabet `Fin d`, the lists below enumerate every word of every
length at most the fixed radius. The resulting first-match selector searches
these addresses and never enumerates the ambient vertex type.
-/

namespace MaxCutGames.Foundations.PCP.PoweringAddresses

open PoweringWalks PoweringLabels
open scoped BigOperators

variable {V : Type*}

/-- A fully executable selector from the explicit bounded address list. -/
def finitePortSelector {d : Nat} [DecidableEq V] (G : PortGraph V (Fin d))
    (t : Nat) (v : V) : AddressSelector G t v :=
  listSelector G t v (allAddresses d t) (mem_allAddresses d t)

end MaxCutGames.Foundations.PCP.PoweringAddresses

/-!
# Executable integer encodings for the powering construction

All encodings below have explicit inverses. They use the arithmetic finite
function, sigma, and product equivalences rather than choosing enumerations
from cardinality proofs. Word digits use the head-major convention; addresses
are grouped by increasing word length. A dart is numbered first by its vertex,
then its word, with its two orientations adjacent.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringOpinionTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Bounded first-address tables for actual powering constraints

For a graph with numbered vertices and ports, each stored local-opinion index
is the first address in `allAddresses` that reaches the requested vertex.
The search traverses bounded port words, never the ambient vertex set.

The walk table stores one base dart and two address indices per traversed
edge. Looking up the endpoint labels at those indices gives exactly the
existing `finitePortSelector` decoders, including when addresses collide.
The resulting finite table predicate equals the actual powering predicate.
-/

namespace MaxCutGames.Foundations.PCP.PoweringOpinionTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open scoped BigOperators

variable {X A : Type*}

variable {vertices d : Nat}

def addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) : AddressIndex d t :=
  firstIndex (fun w => (wordToBall G t center w).val = u.val)
    (allAddresses d t) (by
      obtain ⟨w, hw⟩ := wordToBall_surjective G t center u
      exact ⟨w, mem_allAddresses d t w, congrArg Subtype.val hw⟩)

theorem addressIndex_get (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) :
    (allAddresses d t).get (addressIndex G t center u) =
      (finitePortSelector G t center).address u := by
  change (allAddresses d t).get (firstIndex
    (fun w => (wordToBall G t center w).val = u.val) (allAddresses d t) _) =
      (scanWitness _ _ _).val
  exact get_firstIndex _ _ _

/-- Materialize a padded label in the common address order. -/
def labelTable {t : Nat} (a : PaddedLabel (Fin d) t A) : LabelTable d t A :=
  Vector.ofFn fun i => a ((allAddresses d t).get i)

@[simp] theorem labelTable_get {t : Nat} (a : PaddedLabel (Fin d) t A)
    (i : AddressIndex d t) :
    (labelTable a)[i] = a ((allAddresses d t).get i) := by
  simp [labelTable]

/-- Exact evaluation bridge for every local target, with no consistency
assumption on labels at distinct addresses that reach the same vertex. -/
theorem labelTable_addressIndex (G : PortGraph (Fin vertices) (Fin d)) (t : Nat)
    (center : Fin vertices) (u : Ball G t center) (a : PaddedLabel (Fin d) t A) :
    (labelTable a)[addressIndex G t center u] =
      decode (finitePortSelector G t center) a u := by
  rw [labelTable_get, addressIndex_get]
  rfl

/-- One finite row for each constraint checked along a recorded walk. -/
structure WalkOpinionRow (vertices d t : Nat) where
  edge : Edge (Fin vertices) (Fin d)
  tailIndex : AddressIndex d t
  headIndex : AddressIndex d t

abbrev WalkRows (vertices d n : Nat) := Vector (WalkOpinionRow vertices d (n + 1)) (n + 1)

/-- The only target vertices inspected are the actual edge endpoints. -/
def walkRows (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) : WalkRows vertices d n :=
  Vector.ofFn fun k =>
    { edge := edgeAt G n w k
      tailIndex := addressIndex G (n + 1) w.1 (tailFromStart G n w k)
      headIndex := addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) }

@[simp] theorem walkRows_edge (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1)) :
    (walkRows G n w)[k].edge = edgeAt G n w k := by
  simp [walkRows]

@[simp] theorem walkRows_tail_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (a : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable a)[(walkRows G n w)[k].tailIndex] =
      decode (finitePortSelector G (n + 1) w.1) a (tailFromStart G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) w.1 (tailFromStart G n w k) a

@[simp] theorem walkRows_head_value (G : PortGraph (Fin vertices) (Fin d)) (n : Nat)
    (w : Walk (Fin vertices) (Fin d) (n + 1)) (k : Fin (n + 1))
    (b : PaddedLabel (Fin d) (n + 1) A) :
    (labelTable b)[(walkRows G n w)[k].headIndex] =
      decode (finitePortSelector G (n + 1) (endpoint G w)) b (headFromEnd G n w k) := by
  simpa only [walkRows, Fin.getElem_fin, Vector.getElem_ofFn] using
    labelTable_addressIndex G (n + 1) (endpoint G w) (headFromEnd G n w k) b

end MaxCutGames.Foundations.PCP.PoweringOpinionTables

/-!
# Executable directed graph tables over a fixed finite alphabet

The alphabet size `q` is fixed by the encoding, not encoded as a variable input
field. The header stores vertex and directed-dart counts. Each ordered dart row
stores its tail, reverse index, and every `q*q` predicate bit in order `b+q*a`.
All fields use the existing unary natural-word codec. Decoding validates graph
laws and preserves loops and repeated darts. Size bounds count the complete
serialized table and make no running-time assertion.
-/

namespace MaxCutGames.Foundations.PCP.GenericGraphTables

open MaxCutGames.Foundations.Complexity

variable {q : Nat}

/-- Explicit enumerations determine every vertex name, dart position, and
predicate label. No hidden choice of a graph representation is made. -/
def enumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) :
    ConstraintGraph (Fin n) (Fin m) (Label q) where
  reverse := (dartOrder.symm.trans G.reverse).trans dartOrder
  reverse_involutive e := by
    change dartOrder (G.reverse (dartOrder.symm
      (dartOrder (G.reverse (dartOrder.symm e))))) = e
    rw [dartOrder.symm_apply_apply, G.reverse_involutive, dartOrder.apply_symm_apply]
  tail e := vertexOrder (G.tail (dartOrder.symm e))
  accepts e a b := G.accepts (dartOrder.symm e) (labelOrder.symm a) (labelOrder.symm b)
  reverse_accepts e a b := by
    change G.accepts (dartOrder.symm (dartOrder (G.reverse (dartOrder.symm e))))
      (labelOrder.symm b) (labelOrder.symm a) = _
    rw [dartOrder.symm_apply_apply]
    exact G.reverse_accepts _ _ _

def ofEnumeratedGraph {V E A : Type*} {n m : Nat} (G : ConstraintGraph V E A)
    (vertexOrder : V ≃ Fin n) (dartOrder : E ≃ Fin m) (labelOrder : A ≃ (Label q)) : (Table q) :=
  ofGraph (enumeratedGraph G vertexOrder dartOrder labelOrder)

end MaxCutGames.Foundations.PCP.GenericGraphTables

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTables

open PoweringWalks PoweringLabels PoweringAddresses PoweringEnumeration

def mathematicalGraph {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    ConstraintGraph (Fin vertices) (PoweringTest.Dart (Fin vertices) (Fin d) n)
      (PaddedLabel (Fin d) (n + 1) (Fin 64)) :=
  PoweringTest.poweredGraph (PortTables.portGraph input) (PortTables.accepts input) n
    (finitePortSelector (PortTables.portGraph input) (n + 1))

def table {vertices d : Nat} (input : PortTables.Table vertices d) (n : Nat) :
    GenericGraphTables.Table (labelCount d n) :=
  GenericGraphTables.ofEnumeratedGraph (mathematicalGraph input n) (Equiv.refl _)
    (dartEquiv vertices d n) (paddedLabelEquiv d (n + 1) 64)

@[simp] theorem table_vertices {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).vertices = vertices := rfl

@[simp] theorem table_darts {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) : (table input n).darts = dartCount vertices d n := rfl

end MaxCutGames.Foundations.PCP.PoweringTables

/-!
# Actual rejection counts and sizes for the powering construction

Normalized rejection averages are the cardinal ratios of the corresponding
rejected-dart sets. These identities include empty finite types. Positivity
of the dart cardinality is required only when translating inequalities by
division. The powered dart count and common alphabet size are computed from
their actual product and function types.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringTableSemantics
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
# Exact semantics of the executable powering tables

The explicit label and dart bijections preserve every actual edge test and
every rejected directed occurrence. The inverse label map covers all encoded
assignments, so satisfiability and uniform rejection-count bounds transport
without any consistency restriction on padded labels.
-/


/-!
An actual incidence constraint graph for a finite Boolean verifier with q queries.
Left labels are complete local answer tuples. Their validity includes consistency
at repeated proof addresses. A dart checks the tuple at the least position naming
its proof address. Both sides use the same 2^q-element alphabet; arbitrary right
labels are explicitly decoded by their first coordinate, and honest right labels
are constant tuples. Every incidence is represented by two opposite darts.

The count theorem proves a loss of exactly q in a supplied verifier rejection
fraction. It supplies a concrete construction, not a PCP-hardness premise. The
generic count statements permit an empty event type and introduce no dummy darts.
-/

namespace MaxCutGames.Foundations.PCP.QueryIncidence

variable {E X : Type*} {q : Nat}

def graph [DecidableEq X] (T : Verifier E X q) (positive : 0 < q) :
    ConstraintGraph (Vertex E X) (Dart E q) (Label q) where
  reverse := reverseEquiv
  reverse_involutive := reverse_involutive
  tail := tail T
  accepts := predicate T positive
  reverse_accepts := by
    rintro ⟨⟨event, slot⟩, orientation⟩ a b
    cases orientation <;> rfl

end MaxCutGames.Foundations.PCP.QueryIncidence



end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AlphabetRetraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Pull a graph predicate back through a surjective label decoder.  This preserves
every rejection count after decoding.  A concrete section embeds the initial
eight-label graph into the fixed 64-label alphabet used throughout amplification.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetRetraction

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

@[simp] theorem decode_encode64 (label : InitialGraph.Label) :
    decode64 (encode64 label) = label := by
  rcases label with ⟨a, b, c⟩
  rfl

end MaxCutGames.Foundations.PCP.AlphabetRetraction

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AlphabetReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The explicit assignment tester applied to the encoded satisfying pairs of an
actual finite edge predicate.  The resulting soundness loss is independent of
the alphabet size.  Uniform padding of the finite sample space and assembly of
the global incidence graph are separate constructions.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.AlphabetReduction

open MaxCutGames.Foundations.Hastad
open CodeComposition

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def pairEncoding (accepts : A → A → Bool) (p : LegalPair accepts) :
    InputCoordinate A → Bool :=
  pairWord (codeword p.1.1) (codeword p.1.2)

end MaxCutGames.Foundations.PCP.AlphabetReduction
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_AlphabetGraph
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Foundations.PCP.AlphabetTable.Relations.repeatedConsistentDecidable _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Foundations.PCP.AlphabetGraph

open MaxCutGames.Foundations.Hastad
open scoped BigOperators

variable {V E A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev legal (G : ConstraintGraph V E A) (e : E) (p : A × A) : Prop :=
  G.accepts e p.1 p.2 = true

instance legalDecidable (G : ConstraintGraph V E A) (e : E) :
    DecidablePred (legal G e) :=
  fun p => inferInstanceAs (Decidable (G.accepts e p.1 p.2 = true))

def restrictTape (G : ConstraintGraph V E A) (e : E) (f : Cube (A × A)) :
    Cube (AlphabetReduction.LegalPair (G.accepts e)) := UniformRestriction.restrict (legal G e) f

def extendTape (G : ConstraintGraph V E A) (e : E)
    (f : Cube (AlphabetReduction.LegalPair (G.accepts e))) : Cube (A × A) :=
  UniformRestriction.extend (legal G e) f

def globalizeQuery (G : ConstraintGraph V E A) (e : E) :
    AlphabetReduction.InputCoordinate A ⊕ Cube (AlphabetReduction.LegalPair (G.accepts e)) → Address V E A
  | .inl (side, tape) => .inl ((if side then G.head e else G.tail e), tape)
  | .inr tape => .inr (e, extendTape G e tape)

def verifier (G : ConstraintGraph V E A) : QueryIncidence.Verifier (Event E A) (Address V E A) 6 where
  query := fun (e, kind, k, f, g, r₀, r₁, r₂) slot =>
    globalizeQuery G e (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding (G.accepts e)) kind k
      (restrictTape G e f) (restrictTape G e g) (restrictTape G e r₀)
      (restrictTape G e r₁) (restrictTape G e r₂) slot)
  accepts := fun (_, kind, _, _, _, _, _, _) b => AssignmentTester.eventAccepts kind b

def graph [DecidableEq V] [DecidableEq E] (G : ConstraintGraph V E A) :
    ConstraintGraph (QueryIncidence.Vertex (Event E A) (Address V E A))
      (QueryIncidence.Dart (Event E A) 6) (QueryIncidence.Label 6) := QueryIncidence.graph (verifier G) (by omega)

end MaxCutGames.Foundations.PCP.AlphabetGraph

end

/-!
# Explicit orders for the alphabet-reduction table

All executable maps use Boolean digits, finite sums, and division/remainder.
No enumeration is chosen from a cardinality proof. Cube coordinate zero is the
least significant bit; pairs of coordinates use row-major order. Event blocks
are ordered by their original dart, followed by the local event. Vertices put
events before vertex addresses before edge addresses. Each event has twelve
ordered darts: six slots, with false then true orientation at each slot.
-/

/-! Executable six-query generation on fixed full Boolean cubes. The event
type is exactly `AlphabetGraph.LocalEvent`, including all five full tapes.
Only the returned joint-table addresses are masked outside the input relation;
no legal-pair enumeration or change of sample multiplicities occurs. -/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Queries

open MaxCutGames.Foundations.Hastad

/-- Attach the actual endpoints and edge identifier to a local raw address. -/
def globalize {q : Nat} {V E : Type*} (tail head : V) (edge : E) :
    RawQuery q → AlphabetGraph.Address V E (Fin q)
  | .inl (side, tape) => .inl ((if side then head else tail), tape)
  | .inr tape => .inr (edge, tape)

/-- Proof-only comparison map: extend the original legal-coordinate addresses.
The executable `query` function above never calls this map. -/
def extendQuery {q : Nat} (P : Fin q → Fin q → Bool) :
    AlphabetReduction.InputCoordinate (Fin q) ⊕ Cube (AlphabetReduction.LegalPair P) →
      RawQuery q
  | .inl k => .inl k
  | .inr tape => .inr (UniformRestriction.extend (fun p : Fin q × Fin q => P p.1 p.2 = true) tape)

/-- Pointwise equality with the existing tester after restricting all five
full input tapes and canonically extending the resulting query. The statement
does not require any legal pair to exist. -/
theorem query_eq_extend_eventQueries {q : Nat} (P : Fin q → Fin q → Bool)
    (kind : Fin 4) (k : AlphabetReduction.InputCoordinate (Fin q))
    (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) (slot : Fin 6) :
    query P (kind, k, f, g, r₀, r₁, r₂) slot =
      extendQuery P (AssignmentTester.eventQueries (AlphabetReduction.pairEncoding P) kind k
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) f)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) g)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₀)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₁)
        (UniformRestriction.restrict (fun p : Fin q × Fin q => P p.1 p.2 = true) r₂) slot) := by
  by_cases hk₀ : kind = 0 <;> by_cases hk₁ : kind = 1 <;> by_cases hk₂ : kind = 2 <;>
    simp only [query, AssignmentTester.eventQueries, hk₀, hk₁, hk₂, ite_true, if_true, ite_false]
  all_goals split_ifs <;> simp_all only [extendQuery]
  all_goals rfl

theorem globalize_extendQuery {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E)
    (x : AlphabetReduction.InputCoordinate (Fin q) ⊕
      Cube (AlphabetReduction.LegalPair (G.accepts e))) :
    globalize (G.tail e) (G.head e) e (extendQuery (G.accepts e) x) =
      AlphabetGraph.globalizeQuery G e x := by
  cases x with
  | inl k => cases k; rfl
  | inr tape => rfl

/-- The executable raw queries are exactly the actual verifier queries after
attaching the endpoints and edge tag. This includes self-loops, duplicate
queries, empty legal relations, and every original five-tape event. -/
theorem globalize_query {q : Nat} {V E : Type*}
    (G : ConstraintGraph V E (Fin q)) (e : E) (event : LocalEvent q) (slot : Fin 6) :
    globalize (G.tail e) (G.head e) e (query (G.accepts e) event slot) =
      (AlphabetGraph.verifier G).query (e, event) slot := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rw [query_eq_extend_eventQueries]
  exact globalize_extendQuery G e _

end MaxCutGames.Foundations.PCP.AlphabetTable.Queries

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Relations
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace MaxCutGames.Foundations.PCP.AlphabetTable.Relations

open Hastad
open Queries

variable {q : Nat}

theorem globalize_eq_iff {V E : Type*} [DecidableEq V]
    (tail head : V) (edge : E) (selfLoop : Bool)
    (hloop : selfLoop = decide (tail = head)) (x y : RawQuery q) :
    globalize tail head edge x = globalize tail head edge y ↔
      sameAddress selfLoop x y = true := by
  rcases x with ⟨side, f⟩ | f <;> rcases y with ⟨side', g⟩ | g
  · cases side <;> cases side'
    · simp [globalize, sameAddress]
    · simp [globalize, sameAddress, hloop]
    · simp [globalize, sameAddress, hloop,
        show head = tail ↔ tail = head from eq_comm]
    · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]
  · simp [globalize, sameAddress]


variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
theorem eqProfile_query_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (i j : Fin 6) :
    eqProfile (decide (G.tail e = G.head e)) (query (G.accepts e) event) i j = true ↔
      (AlphabetGraph.verifier G).query (e, event) i =
        (AlphabetGraph.verifier G).query (e, event) j := by
  rw [← globalize_query G e event i, ← globalize_query G e event j]
  exact (globalize_eq_iff (G.tail e) (G.head e) e _ rfl _ _).symm

theorem canonicalSlot_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) :
    canonicalSlot (decide (G.tail e = G.head e)) (query (G.accepts e) event) slot =
      QueryIncidence.canonicalSlot (AlphabetGraph.verifier G) (e, event) slot := by
  unfold canonicalSlot QueryIncidence.canonicalSlot
  apply Fin.find_congr'
  exact eqProfile_query_iff G e event _ slot

omit [DecidableEq E] in
theorem repeatedConsistent_iff (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    RepeatedConsistent (decide (G.tail e = G.head e)) (query (G.accepts e) event) label ↔
      QueryIncidence.RepeatedConsistent (AlphabetGraph.verifier G) (e, event) label := by
  constructor
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mpr hij)
  · intro h i j hij
    exact h i j ((eqProfile_query_iff G e event i j).mp hij)

omit [DecidableEq V] [DecidableEq E] in
theorem verifier_accepts (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (label : QueryIncidence.Label 6) :
    (AlphabetGraph.verifier G).accepts (e, event) label =
      AssignmentTester.eventAccepts event.1 label := by
  rcases event with ⟨kind, k, f, g, r₀, r₁, r₂⟩
  rfl

theorem incidenceAccept_eq (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6)
    (left right : QueryIncidence.Label 6) :
    incidenceAccept (decide (G.tail e = G.head e)) (query (G.accepts e) event)
      (AssignmentTester.eventAccepts event.1) slot left right =
      QueryIncidence.incidenceAccept (AlphabetGraph.verifier G) (by decide) (e, event) slot
        left right := by
  simp only [incidenceAccept, QueryIncidence.incidenceAccept, QueryIncidence.LeftValid,
    verifier_accepts, repeatedConsistent_iff, canonicalSlot_eq,
    QueryIncidence.decodeRight, QueryIncidence.zeroSlot]
  rfl

/-- Every stored bit is the actual six-query incidence predicate under the
canonical explicit six-bit label enumeration, including loops and repeats. -/
theorem relationAt_relation_graph (G : ConstraintGraph V E (Fin q)) (e : E)
    (event : AlphabetGraph.LocalEvent (Fin q)) (slot : Fin 6) (orientation : Bool)
    (a b : GraphTables.Label) :
    GraphTables.relationAt
        (relation (G.accepts e) (decide (G.tail e = G.head e)) event slot orientation) a b =
      (AlphabetGraph.graph G).accepts (((e, event), slot), orientation)
        (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b) := by
  rw [relationAt_relation]
  cases orientation <;>
    exact incidenceAccept_eq G e event slot _ _


end MaxCutGames.Foundations.PCP.AlphabetTable.Relations


namespace MaxCutGames.Foundations.PCP.AlphabetTable.Table

variable {q : Nat}

/-- One directed occurrence, without merging repeated queries or equal rows. -/
def rowFromDart (input : GenericGraphTables.Table q)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    GraphTables.DartRow (Enumeration.vertexCount input.vertices input.darts q)
      (Enumeration.dartCount input.darts q) :=
  let edge := dart.1.1.1
  let event := dart.1.1.2
  let slot := dart.1.2
  let old := input.rows[edge]
  let head := input.rows[old.reverseIndex].tail
  { tail := Enumeration.vertexEquiv input.vertices input.darts q
      (if dart.2 then
        .inr (Queries.globalize old.tail head edge
          (Queries.query (GenericGraphTables.relationAt old.relation) event slot))
      else .inl (edge, event))
    reverseIndex := Enumeration.dartEquiv input.darts q (dart.1, !dart.2)
    relation := Relations.relationFromTable old.relation (decide (old.tail = head))
      event slot dart.2 }

/-- The row number decodes to precisely one event/slot/orientation occurrence. -/
def rows (input : GenericGraphTables.Table q) :
    GraphTables.Rows (Enumeration.vertexCount input.vertices input.darts q)
      (Enumeration.dartCount input.darts q) :=
  Vector.ofFn (fun index =>
    rowFromDart input ((Enumeration.dartEquiv input.darts q).symm index))

@[simp] theorem rows_at (input : GenericGraphTables.Table q)
    (index : Fin (Enumeration.dartCount input.darts q)) :
    (rows input)[index] =
      rowFromDart input ((Enumeration.dartEquiv input.darts q).symm index) := by
  simp [rows]

theorem dartRow_ext_inline_Table {n m : Nat} {left right : GraphTables.DartRow n m}
    (ht : left.tail = right.tail) (hr : left.reverseIndex = right.reverseIndex)
    (hp : left.relation = right.relation) : left = right := by
  cases left
  cases right
  cases ht
  cases hr
  cases hp
  rfl

theorem relation_ext_inline_Table {left right : GraphTables.RelationTable}
    (h : ∀ a b, GraphTables.relationAt left a b = GraphTables.relationAt right a b) :
    left = right := by
  apply Vector.ext
  intro i hi
  let labels := GraphTables.relationIndex.symm (⟨i, hi⟩ : Fin 4096)
  have index : GraphTables.relationIndex labels = (⟨i, hi⟩ : Fin 4096) :=
    GraphTables.relationIndex.apply_symm_apply _
  have point := h labels.1 labels.2
  simpa only [GraphTables.relationAt, index, Fin.getElem_fin] using point

section Semantics

/-- The three stored fields agree with the actual alphabet graph at this dart. -/
theorem rowFromDart_eq_graphRow (input : GenericGraphTables.Table q)
    (dart : QueryIncidence.Dart (AlphabetGraph.Event (Fin input.darts) (Fin q)) 6) :
    rowFromDart input dart =
      { tail := Enumeration.vertexEquiv input.vertices input.darts q
          ((AlphabetGraph.graph (GenericGraphTables.semantics input)).tail dart)
        reverseIndex := Enumeration.dartEquiv input.darts q
          ((AlphabetGraph.graph (GenericGraphTables.semantics input)).reverse dart)
        relation := GraphTables.relationOf (fun a b =>
          (AlphabetGraph.graph (GenericGraphTables.semantics input)).accepts dart
            (Enumeration.labelEquiv.symm a) (Enumeration.labelEquiv.symm b)) } := by
  rcases dart with ⟨⟨⟨edge, event⟩, slot⟩, orientation⟩
  apply dartRow_ext_inline_Table
  · cases orientation with
    | false => rfl
    | true =>
      have query := Queries.globalize_query (GenericGraphTables.semantics input)
        edge event slot
      have predicate : (GenericGraphTables.semantics input).accepts edge =
          GenericGraphTables.relationAt input.rows[edge].relation := rfl
      rw [predicate] at query
      simpa only [rowFromDart, AlphabetGraph.graph, QueryIncidence.graph,
        QueryIncidence.tail, GenericGraphTables.semantics_tail,
        ConstraintGraph.head, GenericGraphTables.semantics_reverse,
        ite_true, if_true] using
        congrArg (fun address => Enumeration.vertexEquiv input.vertices input.darts q
          (.inr address)) query
  · rfl
  · apply relation_ext_inline_Table
    intro a b
    rw [GraphTables.relationAt_relationOf]
    have relation := Relations.relationAt_relation_graph (GenericGraphTables.semantics input)
      edge event slot orientation a b
    have predicate : (GenericGraphTables.semantics input).accepts edge =
        Relations.oldPredicate input.rows[edge].relation := rfl
    rw [predicate] at relation

    simpa only [rowFromDart, Relations.relationFromTable,
      GenericGraphTables.semantics_tail, ConstraintGraph.head,
      GenericGraphTables.semantics_reverse] using! relation

/-- Equality of the full row vector, including all multiplicities and reversal indices. -/
theorem rows_eq_graphRows (input : GenericGraphTables.Table q) :
    rows input = GraphTables.graphRows
      (GraphTables.enumeratedGraph (AlphabetGraph.graph (GenericGraphTables.semantics input))
        (Enumeration.vertexEquiv input.vertices input.darts q)
        (Enumeration.dartEquiv input.darts q) Enumeration.labelEquiv) := by
  apply Vector.ext
  intro i hi
  simp only [rows, GraphTables.graphRows, Vector.getElem_ofFn]
  exact rowFromDart_eq_graphRow input
    ((Enumeration.dartEquiv input.darts q).symm ⟨i, hi⟩)

theorem rows_valid (input : GenericGraphTables.Table q) : GraphTables.Valid (rows input) := by
  rw [rows_eq_graphRows]
  exact GraphTables.graphRows_valid _

/-- Actual executable output table. Its validity proof is erased at execution. -/
def build (input : GenericGraphTables.Table q) : GraphTables.Table where
  vertices := Enumeration.vertexCount input.vertices input.darts q
  darts := Enumeration.dartCount input.darts q
  rows := rows input
  valid := rows_valid input

@[simp] theorem build_vertices (input : GenericGraphTables.Table q) :
    (build input).vertices = Enumeration.vertexCount input.vertices input.darts q := rfl

@[simp] theorem build_darts (input : GenericGraphTables.Table q) :
    (build input).darts = Enumeration.dartCount input.darts q := rfl

@[simp] theorem rowList_length (input : GenericGraphTables.Table q) :
    (GraphTables.rowList (build input)).length = Enumeration.dartCount input.darts q := by
  exact GraphTables.rowList_length (build input)

end Semantics

end MaxCutGames.Foundations.PCP.AlphabetTable.Table


/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

namespace MaxCutGames.Foundations.PCP.RawInitialTables

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

end MaxCutGames.Foundations.PCP.RawInitialTables

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

noncomputable section

namespace MaxCutGames.Foundations.PCP.FiniteGraph

/-- Graphs of different finite sizes inhabit one fixed type for iteration. -/
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

end MaxCutGames.Foundations.PCP.FiniteGraph

end

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

namespace MaxCutGames.Foundations.PCP.VerifierToCNF

open Target

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

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

@[simp] theorem mismatchBits_length {q : Nat} (V : FiniteVerifier q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (mismatchBits V A e p).length = q := by simp [mismatchBits]

theorem mismatchFill_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (fillBits (mismatchBits V A e p)).length = q - 3 := by
  have h := fillBits_length (mismatchBits V A e p) (by simpa using hq)
  rw [mismatchBits_length] at h
  omega

def mismatchFill {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) : Bool :=
  (fillBits (mismatchBits V A e p))[j.val]'(by
    rw [mismatchFill_length V hq A e p]
    exact j.isLt)

/-- A computable assignment extension: finite-sum splitting and quotient/remainder
decoding recover the event, pattern, and auxiliary-bit indices. -/
def extendAssignment {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : Fin (outputVariables V) → Bool :=
  Fin.addCases A (fun k : Fin (auxiliaryCount V) =>
    let pair : Fin (V.events * (patterns q).length) × Fin (q - 3) := finProdFinEquiv.symm k
    let ep : Fin V.events × PatternIndex q := finProdFinEquiv.symm pair.1
    mismatchFill V hq A ep.1 ep.2 pair.2)

@[simp] theorem extend_old {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (v : Fin V.«variables») :
    extendAssignment V hq A (oldIndex V v) = A v := by
  simp [extendAssignment, oldIndex]

@[simp] theorem extend_fresh {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) :
    extendAssignment V hq A (freshIndex V e p j) = mismatchFill V hq A e p j := by
  unfold extendAssignment freshIndex auxiliaryCount
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem restrict_extend {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : restrictAssignment V (extendAssignment V hq A) = A := by
  funext v
  exact extend_old V hq A v

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

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
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

end MaxCutGames.Foundations.PCP.VerifierToCNF

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.FinalBooleanVerifier

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

/-! Direct application to the checked alphabet-reduction graph. -/

end MaxCutGames.Foundations.PCP.FinalBooleanVerifier

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete relation addresses for the final Boolean verifier

Six-bit labels use the already checked executable little-endian enumeration.
A twelve-bit CNF pattern is split into its two endpoint labels, then addressed
in the graph table's row-major order. This fixed address map uses the actual
`VerifierToCNF.patternAt` enumeration, so no assumed correspondence between
two enumeration orders is needed. The graph interpretation is an explicit
relabeling of the validated table semantics.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFPattern

open PCP
open scoped BigOperators

/-- Coordinate zero is the least significant bit. -/
abbrev labelEquiv : Label ≃ Fin 64 := AlphabetTable.Enumeration.labelEquiv

def labelIndex (label : Label) : Fin 64 := labelEquiv label

/-- Graph rows store the right endpoint index fastest. -/
def relationAddress (bits : VerifierToCNF.Pattern 12) : Fin 4096 :=
  GraphTables.relationIndex (labelIndex (leftHalf bits), labelIndex (rightHalf bits))

/-- The address is computed from the converter's actual enumerated pattern. -/
def patternRelationIndex (p : VerifierToCNF.PatternIndex 12) : Fin 4096 :=
  relationAddress (VerifierToCNF.patternAt 12 p)

@[simp] theorem patternRelationIndex_eq (p : VerifierToCNF.PatternIndex 12) :
    patternRelationIndex p = relationAddress (VerifierToCNF.patternAt 12 p) := rfl

/-- Interpret the numeric table over its explicitly decoded Boolean labels. -/
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

end MaxCutGames.Foundations.Complexity.FinalCNFPattern

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Input
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Serialization boundaries and direct row lookup for the shared executable
fixed-alphabet graph codec. The alphabet is a fixed parameter. Rows remain in
their stored order, including repeated darts and loops. Word offsets are fixed;
bit offsets are represented by actual encoded prefixes because unary fields
have data-dependent lengths. These are data identities, not runtime certificates.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Setup

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

variable {K Λ σ : Type} [DecidableEq K]

def statement (ports : Ports K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .copyFirst => Reduction.MachineTransfer.loopAt (ports 0) (ports 5) id false
      (labels .copyFirst) (some (labels .copySecond))
  | .copySecond => MachineCopy.forkLoop (ports 5) (ports 0) (ports 1) false
      (labels .copySecond) (some (labels .verticesStart))
  | .verticesStart => SourceMachine.fieldStart (ports 2) (labels .verticesLoop)
  | .verticesLoop => SourceMachine.fieldLoop (ports 1) (ports 2)
      (labels .verticesLoop) (some (labels .dartsStart))
  | .dartsStart => SourceMachine.fieldStart (ports 3) (labels .dartsLoop)
  | .dartsLoop => SourceMachine.fieldLoop (ports 1) (ports 3)
      (labels .dartsLoop) (some (labels .counterFirst))
  | .counterFirst => Reduction.MachineTransfer.loopAt (ports 3) (ports 5) id false
      (labels .counterFirst) (some (labels .counterSecond))
  | .counterSecond => MachineCopy.forkLoop (ports 5) (ports 3) (ports 4) false
      (labels .counterSecond) (some (labels .initialize_))
  | .initialize_ => .push (ports 6) (fun _ => false)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt (ports 6) exit))

end MaxCutGames.Foundations.PCP.AlphabetTable.Setup

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.ReadRelation

open Turing
open MaxCutGames.Foundations.Complexity
open GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K] {q : Nat}

@[instance_reducible] def stateFintype (σ : Type) (q : Nat) [Fintype σ] :
    Fintype (State σ q) := by
  letI := relationFintype q
  exact inferInstance

/-- Read one encoded Boolean into a fixed slot of the finite relation register. -/
def readSlot (source : K) (i : Fin (q * q))
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  .pop source
    (fun state head =>
      ((state.1.1, state.1.2.set i.val (head.getD false) i.isLt), head))
    (.branch (fun state => state.2.getD false)
      (.pop source (fun state _ => (state.1, none)) next)
      (.load (fun state => (state.1, none)) next))

def readSlots (source : K) : List (Fin (q * q)) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) →
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q)
  | [], next => .load (fun state => (state.1, none)) next
  | i :: indices, next => readSlot source i (readSlots source indices next)

/-- Fixed finite program fragment; it can be inserted before any continuation. -/
def readRelation (source : K)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (State σ q)) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readSlots source (List.finRange (q * q)) next

def parser (source : K) (exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ q) :=
  readRelation source (.goto fun _ => exitLabel)

end MaxCutGames.Foundations.PCP.AlphabetTable.ReadRelation

/-!
# An actual finite machine for a fixed-size Boolean block map

The program parameters `N`, `M`, and `F` are fixed. The local register has
exactly `N` bits. A syntactic chain of `N` pops fills that register, and a
syntactic chain of `M` pushes writes `F` of the register. No instruction
applies `F` to an unbounded word. An arbitrary ambient state is preserved,
and the local register is reset before the optional continuation.

TM2 executes a whole finite statement in one transition. The push bound
below separately records the exact `M` pushes in this statement.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Lookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

/-- Six fixed control labels implement row selection. `q` fixes the finite
predicate parser; no data-dependent number is placed in the program syntax. -/
def statement (q : Nat) (counter source destination : K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard counter (labels .skipTail) (labels .select)
  | .skipTail => MachineLookup.discard source (labels .skipTail) (labels .skipReverse)
  | .skipReverse => MachineLookup.discard source (labels .skipReverse) (labels .skipPredicate)
  | .skipPredicate => skipBits source (q * q) (.goto fun _ => labels .guard)
  | .select => Hastad.SourceMachine.fieldStart destination (labels .copy)
  | .copy => Hastad.SourceMachine.fieldLoop source destination (labels .copy) exit

def rowBits {q n m : Nat} (row : DartRow q n m) : List Bool := encodeWords (rowWords row)

@[simp] theorem rowsBits_cons {q n m : Nat} (row : DartRow q n m)
    (rows : List (DartRow q n m)) : rowsBits (row :: rows) = rowBits row ++ rowsBits rows := by
  simp only [rowsBits, List.flatMap_cons, encodeWords_append, rowBits]

end MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.RuntimeModel

open Turing
open MaxCutGames.Foundations.Complexity

def initial (q : Nat) : State q := normal (Vector.replicate (q * q) false) false

def emitterEquiv (q : Nat) : ((Ambient q × Unit) × Option Bool) ≃ State q where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv s := by rcases s with ⟨⟨s, u⟩, r⟩; cases u; rfl
  right_inv _ := rfl

variable {Λ : Type} {q : Nat}

def emitterStatement (stmt : TM2.Stmt Alphabet Λ ((Ambient q × Unit) × Option Bool)) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (emitterEquiv q) stmt

def nextRow (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .push .edge (fun _ => true)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

end MaxCutGames.Foundations.PCP.AlphabetTable.RuntimeModel

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_EmitRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual alphabet-reduction row template. The old predicate and the loop flag
are finite registers. All unbounded quantities reside in five preserved unary
tapes. The fixed event/slot/orientation order is retained without deduplication.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.EmitRows

open Turing
open MaxCutGames.Foundations.Complexity
open Emitter

def blockWords {q : Nat} (input : GenericGraphTables.Table q)
    (edge : Fin input.darts) : List Nat :=
  (Enumeration.localEvents q).flatMap fun event =>
    (List.finRange 6).flatMap fun slot =>
      [false, true].flatMap fun orientation =>
        GraphTables.rowWords (Table.rowFromDart input (((edge, event), slot), orientation))

end MaxCutGames.Foundations.PCP.AlphabetTable.EmitRows

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

omit [DecidableEq K] in
@[simp] theorem instruction_finish {n : Nat} (selected : Fin n → K)
    (labels : Fin (n + 1) → Λ) (initial : σ) (exit : Option Λ) :
    instruction selected labels initial exit (Fin.last n) = finish initial exit := by
  simp [instruction]

end MaxCutGames.Foundations.PCP.AlphabetTable.Cleanup

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Driver

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open RuntimeModel

def headerEntry (q : Nat) : Label q :=
  .header (Emitter.labelAt (headerPlan q).length (Addresses.fieldBound q) 0 .entry)

def rowEntry (q : Nat) : Label q :=
  .emit (Emitter.labelAt (rowPlan q).length (Addresses.fieldBound q) 0 .entry)

def program (q : Nat) : Label q → TM2.Stmt Alphabet (Label q) (State q)
  | .setup label => Setup.statement setupPorts Label.setup (some (headerEntry q)) label
  | .header label => emitterStatement
      (Emitter.statement (Emitter.listCommands (headerPlan q)) headerSources .scratch .reversed
        Label.header (some .guard) label)
  | .guard => MachineUnaryCounter.guard .counter .tailStart .reverseOutput
  | .tailStart => SourceMachine.fieldStart .tail .tailLoop
  | .tailLoop => SourceMachine.fieldLoop .cursor .tail .tailLoop (some .reverseStart)
  | .reverseStart => SourceMachine.fieldStart .reverseIndex .reverseLoop
  | .reverseLoop => SourceMachine.fieldLoop .cursor .reverseIndex .reverseLoop (some .readPredicate)
  | .readPredicate => ReadRelation.parser .cursor .headCopyFirst
  | .headCopyFirst => Reduction.MachineTransfer.loopAt .original .scratch id false
      .headCopyFirst (some .headCopySecond)
  | .headCopySecond => MachineCopy.forkLoop .scratch .original .scan false
      .headCopySecond (some .indexCopyFirst)
  | .indexCopyFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .indexCopyFirst (some .indexCopySecond)
  | .indexCopySecond => MachineCopy.forkLoop .scratch .reverseIndex .indexScan false
      .indexCopySecond (some .headVertices)
  | .headVertices => MachineLookup.discard .scan .headVertices .headDarts
  | .headDarts => MachineLookup.discard .scan .headDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement q .indexScan .scan .head Label.headLookup
      (some (.compare .leftFirst)) label
  | .compare label => CompareLoop.statement Label.compare (rowEntry q) label
  | .emit label => emitterStatement
      (Emitter.statement (Emitter.listCommands (rowPlan q)) rowSources .scratch .reversed
        Label.emit (some (.clearField 0)) label)
  | .clearField slot => MachineDrain.drain (fieldPorts slot) (.clearField slot)
      (some (clearNext slot))
  | .increment => nextRow .guard
  | .reverseOutput => Reduction.MachineTransfer.loopAt .reversed .output id false
      .reverseOutput (some (.cleanup 0))
  | .cleanup slot => Cleanup.instruction cleanupPorts Label.cleanup (initial q).1 none slot

@[simp] theorem program_setup (q : Nat) (label : Setup.Label) :
    program q (.setup label) =
      Setup.statement setupPorts Label.setup (some (headerEntry q)) label := rfl

@[simp] theorem program_guard (q : Nat) : program q .guard =
    MachineUnaryCounter.guard .counter .tailStart .reverseOutput := rfl

@[simp] theorem program_headLookup (q : Nat) (label : Lookup.Label) :
    program q (.headLookup label) = Lookup.statement q .indexScan .scan .head
      Label.headLookup (some (.compare .leftFirst)) label := rfl

@[simp] theorem program_compare (q : Nat) (label : CompareLoop.Label) :
    program q (.compare label) = CompareLoop.statement Label.compare (rowEntry q) label := rfl

@[simp] theorem program_increment (q : Nat) : program q .increment = nextRow .guard := rfl

end MaxCutGames.Foundations.PCP.AlphabetTable.Driver

/-!
Exact tape invariant for the old-dart loop. The cursor stores the remaining
input rows, while the reversed tape stores precisely the output headers and
the blocks already emitted. The scan and index-scan tapes are unconstrained:
the next lookup prefixes fresh copies and retains old residues as suffixes.
Finite control state is specified by the actual execution theorems using this
tape invariant.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.LoopState

open MaxCutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

/-- The output headers are included even before the first old row is read. -/
def prefixWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q] ++
    ((List.finRange input.darts).take e).flatMap (EmitRows.blockWords input)

def prefixBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (prefixWords input e)

def cursorWords (input : GenericGraphTables.Table q) (e : Nat) : List Nat :=
  ((GenericGraphTables.rowList input).drop e).flatMap GenericGraphTables.rowWords

def cursorBits (input : GenericGraphTables.Table q) (e : Nat) : List Bool :=
  encodeWords (cursorWords input e)

@[simp] theorem prefixWords_zero (input : GenericGraphTables.Table q) :
    prefixWords input 0 =
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  simp [prefixWords]

@[simp] theorem prefixBits_zero (input : GenericGraphTables.Table q) :
    prefixBits input 0 = encodeWords
      [Enumeration.vertexCount input.vertices input.darts q,
        Enumeration.dartCount input.darts q] := by
  rw [prefixBits, prefixWords_zero]

@[simp] theorem cursorBits_zero (input : GenericGraphTables.Table q) :
    cursorBits input 0 =
      encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords) := by
  simp [cursorBits, cursorWords]

end MaxCutGames.Foundations.PCP.AlphabetTable.LoopState

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryParsing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Soundness of the ordinary-binary parser and its concrete name-scanning machine.
Every successful parse consumes exactly a canonical encoding and leaves its
stated suffix. Thus malformed or noncanonical bitstrings cannot name an extra
formula. The finite scanner's final-digit test is proved equivalent to the
codec's arithmetic canonicality test.
-/

/-!
Occurrence-index renaming for the ordinary-binary input machine. Every name is
replaced by the position of its first occurrence in the complete literal-name
list. The output declares three «variables» per clause; some IDs can be unused.
This avoids constructing a duplicate-free dictionary while keeping all IDs
bounded by the literal occurrence count. Equality tests may compare the actual
canonical binary payloads, without converting a name to unary.

These are the correspondence facts for the scan/compare machine.
They do not by themselves assert that the renaming runs in polynomial time.
-/

/-!
The ordinary binary 3SAT language includes exactly the successfully decoded
satisfiable formulas. A total semantic extension of occurrence-index renaming
maps malformed bitstrings to a fixed contradictory formula. Its runtime is a
separate machine-composition obligation; the size theorem below is only size.
-/

namespace MaxCutGames.BinaryLanguage

open MaxCutGames.Foundations

theorem rejectBinary_unsatisfiable : ¬rejectBinary.Satisfiable := by
  rintro ⟨assignment, satisfied⟩
  have positive := satisfied #v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩]
    (by simp [rejectBinary])
  have negative := satisfied #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]
    (by simp [rejectBinary])
  cases h : assignment 0 <;>
    simp [BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, h] at positive negative

end MaxCutGames.BinaryLanguage

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryNameCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Compare one framed binary name with an already extracted reversed key.
The candidate stream loses precisely that name frame. The key and every other
non-work stack are preserved; the three work stacks are empty again on exit.
The scanner, copy loops, and head-by-head comparison all execute actual TM2
instructions. Whole words occur only in the correctness specification.
-/

/-!
First-occurrence search over signed, framed binary names. The stream has no
clause markers. Every iteration discards one sign, scans and compares the
actual candidate payload, and increments a Boolean unary counter only after a
mismatch. The preserved key is a reversed payload, never a unary name.

The six explicitly distinct tapes are: stream, preserved key, candidate,
copied key, copy scratch, and unary occurrence counter. Successful search
consumes precisely the prefix through the first matching name, preserves the
unread suffix and all ambient tapes, and returns the three work tapes empty.
The time theorem follows from literal instruction equations and checked
comparison executions, with no supplied loop-body trace premise.
-/

namespace MaxCutGames.BinaryNameSearch

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

/-- Work is linear in the scanned payloads plus one key-copy cost per token. -/
theorem steps_le (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ 2 * payloadSize tokens + (3 * key.length + 6) * tokens.length := by
  induction tokens with
  | nil => simp [steps]
  | cons token tokens ih =>
      have h := BinaryNameCompare.steps_le token.2.length key.length
      simp only [steps, payloadSize_cons, List.length_cons]
      split <;> nlinarith

/-- This bound uses lengths of actual encoded words, not decoded name values. -/
theorem steps_le_stream (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ (3 * key.length + 7) * (stream tokens).length := by
  have h := steps_le tokens key
  rw [stream_length]
  nlinarith

end MaxCutGames.BinaryNameSearch

namespace MaxCutGames.BinaryLiteralMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

theorem afterMatch_length_le (tokens : List BinaryNameSearch.Token) (bits : List Bool) :
    (BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length ≤
      (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp [BinaryNameSearch.afterMatch]
  | cons token tokens ih =>
      simp only [BinaryNameSearch.afterMatch, BinaryNameSearch.stream_cons, List.length_append]
      split <;> omega

theorem steps_le (tokens : List BinaryNameSearch.Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    steps tokens bits ≤
      3 * ((BinaryNameSearch.stream tokens).length + bits.length) ^ 2 +
        13 * ((BinaryNameSearch.stream tokens).length + bits.length) + 9 := by
  have search := BinaryNameSearch.steps_le_stream tokens bits
  have suffix := afterMatch_length_le tokens bits
  have idx : index tokens bits < tokens.length := by
    have h := List.idxOf_lt_length_iff.mpr present
    simpa [index, BinaryNameSearch.payloads] using h
  have count : tokens.length ≤ (BinaryNameSearch.stream tokens).length := by
    rw [BinaryNameSearch.stream_length]
    omega
  unfold steps
  nlinarith [Nat.zero_le ((BinaryNameSearch.stream tokens).length * bits.length)]

end MaxCutGames.BinaryLiteralMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryRenameLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The actual cursor loop for sparse-name renaming. A finite three-position slot
counts completed clauses. Each nonempty cursor test calls the checked literal
machine, then pushes one variable-count bit. Every third literal also pushes
one clause-count bit. No instruction counts an unbounded list in finite control.

All nine literal-machine tapes retain their meanings. Tapes 9 and 10 are the
variable and clause counters. The original token stream is preserved; the
cursor is exhausted, the six work tapes are restored, and the output contains
the reversed concatenation of exactly the emitted literal words.
-/

namespace MaxCutGames.BinaryRenameLoop

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition

theorem payload_length_le_stream (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    bits.length ≤ (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp at present
  | cons token tokens ih =>
      rcases List.mem_cons.mp present with equal | remaining
      · rw [equal]
        simp only [BinaryNameSearch.stream_cons, List.length_append,
          BinaryNameSearch.tokenBits, List.length_cons, BinaryNameMachine.frame_length]
        omega
      · have tail := ih remaining
        simp only [BinaryNameSearch.stream_cons, List.length_append]
        omega

theorem literal_steps_le (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    BinaryLiteralMachine.steps tokens bits + 2 ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length := by
  have body := BinaryLiteralMachine.steps_le tokens bits present
  have size := payload_length_le_stream tokens bits present
  have sumBound : (BinaryNameSearch.stream tokens).length + bits.length ≤
      2 * (BinaryNameSearch.stream tokens).length := by omega
  have sq := Nat.mul_self_le_mul_self sumBound
  unfold perLiteralBound
  nlinarith

theorem steps_le (tokens input : List Token) (included : ∀ token ∈ input, token ∈ tokens) :
    steps tokens input ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length * input.length + 1 := by
  induction input with
  | nil => simp [steps]
  | cons token input ih =>
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, included token (by simp), rfl⟩
      have head := literal_steps_le tokens token.2 present
      have tail := ih (fun t ht => included t (by simp [ht]))
      simp only [steps, List.length_cons]
      nlinarith

end MaxCutGames.BinaryRenameLoop

/-!
An actual finite Boolean-stack machine which removes formula/clause markers
from valid ordinary-binary 3CNF encodings. Literal signs and every bit of each
framed binary name survive in their original occurrence order. The first pass
accumulates the output in reverse; the checked transfer routine restores order.

The machine is specified on the semantic encoded-input domain. It does not
claim to reject every malformed or noncanonical input. In particular, the
name-copying loop does not check canonicality: valid input already supplies it.
All transitions inspect only finite control and one popped bit. No branch or
load computes a whole-list function or converts a binary name to unary.
-/

namespace MaxCutGames.BinaryTokenMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer
open BinaryFormula BinaryEncoding

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end MaxCutGames.BinaryTokenMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryRenameWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The word-level correspondence used by the ordinary-binary renaming machine.
Literal occurrences stay in clause order, and equality is tested on canonical
binary payloads. The output body consists of the first occurrence index and
the sign of every literal, in the inherited dense formula codec.
-/

namespace MaxCutGames.BinaryRenameWords

open BinaryFormula MaxCutGames.Foundations

theorem encoded_clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Complexity.encodeWords (Complexity.clauseWords (BinaryOccurrenceRename.clause F c mem)) =
      (clauseLiterals c).flatMap (outputLiteral (sourceNames F)) := by
  simp [Complexity.clauseWords, Complexity.literalWords, Complexity.encodeWords,
    BinaryOccurrenceRename.clause, BinaryOccurrenceRename.literal,
    BinaryOccurrenceRename.nameIndex, clauseLiterals, outputLiteral, List.append_assoc]
  rfl

theorem encodeWords_flatMap_inline_MachineBinaryRenameWords {α : Type} (xs : List α) (f : α → List Nat) :
    Complexity.encodeWords (xs.flatMap f) =
      xs.flatMap (fun x => Complexity.encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, Complexity.encodeWords_append, ih]

/-- The output contains every literal occurrence, including repetitions. -/
theorem encoded_body (F : Formula) :
    Complexity.encodeWords ((BinaryOccurrenceRename.renamed F).clauses.flatMap
      Complexity.clauseWords) = body F := by
  rw [encodeWords_flatMap_inline_MachineBinaryRenameWords]
  change (F.clauses.attach.map (fun c => BinaryOccurrenceRename.clause F c.val c.property)).flatMap
    (fun c => Complexity.encodeWords (Complexity.clauseWords c)) = body F
  rw [List.flatMap_map]
  simp only [encoded_clause]
  have h := congrArg (fun cs : List Clause =>
    cs.flatMap (fun c => (clauseLiterals c).flatMap (outputLiteral (sourceNames F))))
    (List.attach_map_subtype_val F.clauses)
  simpa only [List.flatMap_map, body, literals, List.flatMap_assoc] using h

/-- Exact ordinary-binary-machine target, including its two count headers. -/
theorem encoded_renamed (F : Formula) :
    Complexity.formulaBits (BinaryOccurrenceRename.renamed F) =
      Complexity.encodeWord (3 * F.clauses.length) ++
        Complexity.encodeWord F.clauses.length ++ body F := by
  simp only [Complexity.formulaBits, Complexity.formulaWords, Complexity.encodeWords_append,
    Complexity.encodeWords, List.append_nil,
    BinaryOccurrenceRename.renamed_variable_count,
    BinaryOccurrenceRename.renamed_clause_count, encoded_body, List.append_assoc]

end MaxCutGames.BinaryRenameWords

/-!
An actual finite Boolean-stack routine prepending two unary header words to an
already restored serialized body. It consumes counters containing `n` and `m`
true bits, respectively, in exactly `n + m + 4` transitions. All ambient stacks
and the finite ambient state are preserved. The input counters need no separate
counting pass: a caller can accumulate them while constructing the body.

The generic placement theorem uses only four displayed instruction equations.
The concrete machine below has three Boolean stacks and four control labels;
its final transfer halts directly. This is a staged configuration computation,
not a single-input `initList` assertion that silently assumes two extra inputs.
-/

/-!
The finite Boolean-stack driver for first-occurrence renaming. Its permanent
input is copied to a cursor, each literal is translated by the checked search
loop, and the physical output is restored, prefixed with its count headers,
and cleaned up. Every tape uses Bool and every control component is finite.
-/

namespace MaxCutGames.BinaryRenameMachine

open Turing MaxCutGames.Foundations
open Complexity Complexity.MachineComposition
open MaxCutGames.Reduction.MachineTransfer

theorem renameTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[steps formula]
      (some (initList machine (BinaryTokenMachine.tokens formula.clauses))) =
      some (haltList machine (formulaBits (BinaryOccurrenceRename.renamed formula))) := by
  have first := copyTrace (BinaryTokenMachine.tokens formula.clauses)
  have second := loopTrace formula
  have third := restoreTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (List.replicate (3 * formula.clauses.length) true)
    (List.replicate formula.clauses.length true)
  have fourth := headerTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (3 * formula.clauses.length) formula.clauses.length
  have fifth := cleanupTrace (BinaryTokenMachine.tokens formula.clauses)
    (encodeWord (3 * formula.clauses.length) ++ encodeWord formula.clauses.length ++
      BinaryRenameWords.body formula)
  have full := joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine (joinTrace_inline_MachineBinaryRenameMachine first second) third) fourth) fifth
  have count : 3 * formula.clauses.length + formula.clauses.length + 4 =
      4 * formula.clauses.length + 4 := by omega
  simpa only [steps, initList_eq, haltList_eq, BinaryRenameWords.encoded_renamed, count] using full

theorem clause_count_le_stream (formula : BinaryFormula.Formula) :
    formula.clauses.length ≤ (BinaryTokenMachine.tokens formula.clauses).length := by
  rw [BinaryTokenMachine.tokens_length]
  omega

theorem body_length_le (formula : BinaryFormula.Formula) :
    (BinaryRenameWords.body formula).length ≤
      9 * (BinaryTokenMachine.tokens formula.clauses).length ^ 2 +
        10 * (BinaryTokenMachine.tokens formula.clauses).length + 2 := by
  have initial := BinaryOccurrenceRename.renamed_encoding_bound formula
  rw [BinaryRenameWords.encoded_renamed] at initial
  simp only [List.length_append] at initial
  have count := clause_count_le_stream formula
  have square := Nat.mul_self_le_mul_self count
  nlinarith

theorem steps_le (formula : BinaryFormula.Formula) :
    steps formula ≤ timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length := by
  have loopBound := BinaryRenameLoop.steps_le
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    (fun _ h => h)
  rw [BinaryRenameWords.tokens_stream, BinaryRenameWords.tokens_length] at loopBound
  have literalCount : 3 * formula.clauses.length ≤
      (BinaryTokenMachine.tokens formula.clauses).length := by
    rw [BinaryTokenMachine.tokens_length]
    omega
  have product := Nat.mul_le_mul_left
    (BinaryRenameLoop.perLiteralBound (BinaryTokenMachine.tokens formula.clauses).length)
    literalCount
  have output := body_length_le formula
  have count := clause_count_le_stream formula
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold steps BinaryRenameLoop.perLiteralBound at *
  nlinarith

def outputsInTime (formula : BinaryFormula.Formula) :
    TM2OutputsInTime machine (BinaryTokenMachine.tokens formula.clauses)
      (some (formulaBits (BinaryOccurrenceRename.renamed formula)))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length) where
  steps := steps formula
  evals_in_steps := renameTrace formula
  steps_le_m := steps_le formula

/-- The token-stream phase has a displayed finite machine and actual execution
bound; its polynomial argument is the token stream's physical bit length. -/
noncomputable def tokenComputation :
    TM2ComputableInPolyTime (fun formula : BinaryFormula.Formula =>
      BinaryTokenMachine.tokens formula.clauses) formulaBits BinaryOccurrenceRename.renamed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((BinaryTokenMachine.tokens formula.clauses).map id)
      (some ((formulaBits (BinaryOccurrenceRename.renamed formula)).map id))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

/-- Actual finite-alphabet polynomial-time sparse binary to dense unary
renaming. Sparse name magnitudes are never expanded in unary. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits formulaBits
      BinaryOccurrenceRename.renamed :=
  MachineSequential.composeBits preprocessing tokenComputation

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  MachineFiniteAlphabet.composeBits preprocessing tokenComputation
    BinaryTokenMachine.machine_finiteAlphabet machine_finiteAlphabet

end MaxCutGames.BinaryRenameMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open MaxCutGames.Foundations.PCP

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

end MaxCutGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachinePreservingLookupClean

open Turing
open MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- Tape roles: 0 original table, 1 unary index, 2 working copy, 3 output,
4 copy/restore scratch. The embedded halt enters the explicit cleanup loop. -/
def statement (tape : Fin 5 → K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .run label => MachineSubroutine.statement (fun label => labels (.run label))
      (some (labels .cleanup)) (MachinePreservingLookup.program tape label)
  | .cleanup => MachineDrain.drain (tape 2) (labels .cleanup) exit

end MaxCutGames.Foundations.Complexity.MachinePreservingLookupClean

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderRowControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.ExpanderRowControl

open ExpanderTables

/-- Consume the finite cloud coordinate and input port, and perform the first
lookup in the fixed table. Initial register values need no inhabitance choice. -/
def start {d : Nat} (H : Table (cloudSize d) d)
    (cloud : Fin (cloudSize d)) (port : Fin (degree d)) : Control d :=
  let ports := (rowIndex d d).symm port
  let first := lookup H (cloud, ports.1)
  let square := (rowIndex (degree d) (degree d)).symm first.1
  { firstH := first
    lastInput := ports.2
    firstG := square.1
    secondG := square.2
    lastH := first }

/-- The second graph remainder completes the final lookup in the fixed table.
The square return ports are ordered second, first, as in `stepLookup`. -/
def receiveSecond {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (returnedPort : Fin (degree d)) : Control d :=
  { s with
    secondG := returnedPort
    lastH := lookup H
      (rowIndex (degree d) (degree d) (returnedPort,s.firstG),s.lastInput) }

@[simp] theorem receiveSecond_port {d : Nat} (H : Table (cloudSize d) d)
    (s : Control d) (r : Fin (degree d)) : (receiveSecond H s r).secondG = r := rfl

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

/-- Pure row semantics: exactly two lookups in the input table. The two fixed
H lookups occur inside `start` and `receiveSecond`. This is not a machine trace. -/
def evaluateRow {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    Fin v × Control d :=
  let s₀ := start H cloud port
  let g₁ := lookup G (vertex,firstOffset s₀)
  let s₁ := receiveFirst s₀ g₁.2
  let g₂ := lookup G (g₁.1,secondOffset s₁)
  (g₂.1, receiveSecond H s₁ g₂.2)

/-- The finite callback sequence computes exactly the previously checked
square/zigzag lookup, including both reversed square ports. -/
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

/-- The emitted natural number is the actual stored row, not just an
extensionally equivalent endpoint pair. -/
theorem outputAddress_eq_step_reverseIndex {v d : Nat}
    (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (cloud : Fin (cloudSize d)) (port : Fin (degree d)) :
    outputAddress (evaluateRow G H vertex cloud port).1.val (evaluateRow G H vertex cloud port).2 =
      (reverseIndex (step G H) (rowIndex (v * cloudSize d) (degree d)
        (rowIndex v (cloudSize d) (vertex,cloud),port))).val := by
  rw [outputAddress_eq_step_row, rowIndex_lookup]

end MaxCutGames.Foundations.PCP.ExpanderRowControl

/-!
# Raw natural-word serialization of actual expander rotation tables

The list keeps the stored row order `port + degree * vertex`; no header is
inserted. Lookup equalities and complete unary output lengths are data facts,
not machine execution certificates. Kernel-checked with Lean 4.33.1.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTableWords

open ExpanderTables
open MaxCutGames.Foundations.Complexity (encodeWords decodeWords)

variable {v d : ℕ}

def rotationWords (table : Table v d) : List Nat := table.rows.toList.map Fin.val

@[simp] theorem rotationWords_length (table : Table v d) :
    (rotationWords table).length = v * d := by
  simp [rotationWords]

theorem rotationWords_getElem (table : Table v d) (i : ℕ) (hi : i < v * d) :
    (rotationWords table)[i]'(by simpa only [rotationWords_length] using hi) =
      (reverseIndex table ⟨i, hi⟩).val := by
  simp only [rotationWords, List.getElem_map, Vector.getElem_toList,
    reverseIndex, Fin.getElem_fin]

@[simp] theorem decode_rotationWords (table : Table v d) :
    decodeWords (encodeWords (rotationWords table)) = some (rotationWords table) :=
  Complexity.decodeWords_encodeWords _

end MaxCutGames.Foundations.PCP.ExpanderTableWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFixedDivMod
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineFixedDivMod

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord )

variable {K Λ σ : Type} [DecidableEq K]

def unaryTapes (source quotient remainder : K) (base : K → List Bool)
    (n q r : Nat) (sourceSuffix quotientSuffix remainderSuffix : List Bool) : K → List Bool :=
  tapes source quotient remainder base (encodeWord n ++ sourceSuffix)
    (encodeWord q ++ quotientSuffix) (encodeWord r ++ remainderSuffix)

@[simp] theorem unaryTapes_source (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (base : K → List Bool) (n q r : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    unaryTapes source quotient remainder base n q r sourceSuffix quotientSuffix
      remainderSuffix source = encodeWord n ++ sourceSuffix := by
  simp [unaryTapes, sourceQuotient, sourceRemainder]

@[simp] theorem unaryTapes_quotient (source quotient remainder : K)
    (quotientRemainder : quotient ≠ remainder) (base : K → List Bool) (n q r : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    unaryTapes source quotient remainder base n q r sourceSuffix quotientSuffix
      remainderSuffix quotient = encodeWord q ++ quotientSuffix := by
  simp [unaryTapes, quotientRemainder]

@[simp] theorem unaryTapes_remainder (source quotient remainder : K)
    (base : K → List Bool) (n q r : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    unaryTapes source quotient remainder base n q r sourceSuffix quotientSuffix
      remainderSuffix remainder = encodeWord r ++ remainderSuffix := by
  simp [unaryTapes]

end MaxCutGames.Foundations.Complexity.MachineFixedDivMod

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

inductive Label (d : Nat)
  | initialize_
  | firstEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | firstReverse
  | firstLookup (label : MachinePreservingLookupClean.Label)
  | firstScan
  | firstResidue (r : Fin (degree d))
  | clearQuery
  | secondEmit (label : PCP.AlphabetTable.Emitter.Label 3 (degree d))
  | secondReverse
  | secondLookup (label : MachinePreservingLookupClean.Label)
  | secondScan
  | secondResidue (r : Fin (degree d))
  | outputEmit (label : PCP.AlphabetTable.Emitter.Label 3 (rowFactor d))
  | cleanup (i : Fin 6)
  | done
  deriving DecidableEq, Fintype

abbrev Ambient (ρ : Type) (d : Nat) := ρ × Control d
abbrev State (ρ : Type) (d : Nat) :=
  PCP.AlphabetTable.Emitter.State (Ambient ρ d × Fin (degree d))

/-- The residue and the emitter's unit field are just permuted; no tape is
read or written by this static change of finite state coordinates. -/
def divisionStates (ρ : Type) (d : Nat) :
    MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d) ≃ State ρ d where
  toFun s := (((s.1.1.1, s.1.2), ()), s.2)
  invFun s := (((s.1.1.1, ()), s.1.1.2), s.2)
  left_inv := by rintro ⟨⟨⟨a, u⟩, r⟩, b⟩; cases u; rfl
  right_inv := by rintro ⟨⟨⟨a, r⟩, u⟩, b⟩; cases u; rfl

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

/-- Every branch is a concrete finite TM2 statement. The fixed table `H`
is evaluated only on finite control values, never on an unbounded tape value. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
The two actual division phases of the expander-row program. Static state
conjugation connects the fixed-divisor machine to the common emitter state.
Only the concrete statement placement equations are premises; no phase trace
or whole-row execution is assumed. Each phase has exactly `n + 2` transitions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

@[simp] theorem divisionStates_apply (ρ : Type) (d : Nat)
    (s : MachineFixedDivMod.State (Ambient ρ d × Unit) (degree d)) :
    divisionStates ρ d s = (((s.1.1.1, s.1.2), ()), s.2) := rfl

/-- The common row state at a division boundary, with its local residue reset. -/
def divisionState {d : Nat} (positive : 0 < d) (ambient : ρ) (control : Control d)
    (register : Option Bool) : State ρ d :=
  ((((ambient, control),
    MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive) 0), ()), register)

def divisionOutput (d : Nat) (ports : Tape → K) (quotient remainder : Tape)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) : K → List Bool :=
  MachineFixedDivMod.unaryTapes (ports .lookupOutput) (ports quotient) (ports remainder)
    base 0 (n / degree d) (n % degree d) sourceSuffix quotientSuffix remainderSuffix

@[simp] theorem divisionOutput_source (d : Nat) (ports : Tape → K)
    (portsInjective : Function.Injective ports) (quotient remainder : Tape)
    (notSourceQuotient : Tape.lookupOutput ≠ quotient)
    (notSourceRemainder : Tape.lookupOutput ≠ remainder)
    (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports .lookupOutput) = encodeWord 0 ++ sourceSuffix := by
  exact MachineFixedDivMod.unaryTapes_source _ _ _
    (fun h => notSourceQuotient (portsInjective h))
    (fun h => notSourceRemainder (portsInjective h)) _ _ _ _ _ _ _

@[simp] theorem divisionOutput_quotient (d : Nat) (ports : Tape → K)
    (portsInjective : Function.Injective ports) (quotient remainder : Tape)
    (distinct : quotient ≠ remainder) (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports quotient) = encodeWord (n / degree d) ++ quotientSuffix := by
  exact MachineFixedDivMod.unaryTapes_quotient _ _ _
    (fun h => distinct (portsInjective h)) _ _ _ _ _ _ _

@[simp] theorem divisionOutput_remainder (d : Nat) (ports : Tape → K)
    (quotient remainder : Tape) (base : K → List Bool) (n : Nat)
    (sourceSuffix quotientSuffix remainderSuffix : List Bool) :
    divisionOutput d ports quotient remainder base n sourceSuffix quotientSuffix remainderSuffix
      (ports remainder) = encodeWord (n % degree d) ++ remainderSuffix := by
  exact MachineFixedDivMod.unaryTapes_remainder _ _ _ _ _ _ _ _ _ _

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

abbrev Tape := MachineExpanderRow.Tape ⊕ ExtraTape

abbrev Alphabet : Tape → Type :=
  MachineEmbedding.Alphabet (fun _ : MachineExpanderRow.Tape => Bool)
    (fun _ : ExtraTape => Bool)

abbrev Label (d : Nat) := MachineExpanderRow.Label d ⊕ OuterLabel
abbrev State (ρ : Type) (d : Nat) := MachineExpanderRow.State ρ d × Position d
abbrev RowStatePrefix (ρ : Type) (d : Nat) :=
  (MachineExpanderRow.Ambient ρ d × Fin (degree d)) × Unit

/-- Static movement of the bit register to the last product coordinate. -/
def guardStates (ρ : Type) (d : Nat) :
    ((RowStatePrefix ρ d × Position d) × Option Bool) ≃ State ρ d where
  toFun s := ((s.1.1, s.2), s.1.2)
  invFun s := ((s.1.1, s.2), s.1.2)
  left_inv := by rintro ⟨⟨a, p⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, p⟩; rfl

@[simp] theorem guardStates_apply (ρ : Type) (d : Nat)
    (s : (RowStatePrefix ρ d × Position d) × Option Bool) :
    guardStates ρ d s = ((s.1.1, s.2), s.1.2) := rfl

@[simp] theorem guardStates_symm_apply (ρ : Type) (d : Nat) (s : State ρ d) :
    (guardStates ρ d).symm s = ((s.1.1, s.2), s.1.2) := rfl

theorem rowFactor_pos {d : Nat} (positive : 0 < d) : 0 < rowFactor d := by
  have hq : 0 < degree d := Nat.mul_pos positive positive
  exact Nat.mul_pos (Nat.mul_pos hq hq) hq

def zeroPosition {d : Nat} (positive : 0 < d) : Position d :=
  ⟨0, rowFactor_pos positive⟩

def nextPosition {d : Nat} (positive : 0 < d) (p : Position d) : Position d :=
  ⟨(p.val + 1) % rowFactor d, Nat.mod_lt _ (rowFactor_pos positive)⟩

def positionPair {d : Nat} (p : Position d) : Fin (cloudSize d) × Fin (degree d) :=
  (rowIndex (cloudSize d) (degree d)).symm p

def caller {ρ : Type} {d : Nat} (s : State ρ d) : ρ := s.1.1.1.1.1

/-- A fresh row call, with its residue and bit register reset. -/
def boundaryState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) (p : Position d) : State ρ d :=
  (MachineExpanderRow.divisionState positive ambient
    (start H (positionPair p).1 (positionPair p).2) none, p)

def initialState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (ambient : ρ) : State ρ d :=
  boundaryState positive H ambient (zeroPosition positive)

def prepareState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  boundaryState positive H (caller s) s.2

def resetState {ρ : Type} {d : Nat} (positive : 0 < d)
    (H : Table (cloudSize d) d) (s : State ρ d) : State ρ d :=
  initialState positive H (caller s)

def clearRegister {ρ : Type} {d : Nat} (s : State ρ d) : State ρ d :=
  ((s.1.1, none), s.2)

def advancePositionState {ρ : Type} {d : Nat} (positive : 0 < d)
    (s : State ρ d) : State ρ d := (s.1, nextPosition positive s.2)

def resetPositionState {ρ : Type} {d : Nat} (positive : 0 < d)
    (s : State ρ d) : State ρ d := (s.1, zeroPosition positive)

/-- The unary guard specialized to the concrete extra tape. The zero delimiter
is retained; both branches clear the bit register. Its dependent alphabet is
the same alphabet used by the embedded row program. -/
def vertexGuardCore {ρ : Type} {d : Nat} :
    TM2.Stmt Alphabet (Label d) ((RowStatePrefix ρ d × Position d) × Option Bool) :=
  .peek (.inr .vertexCount) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.pop (.inr .vertexCount) (fun s _ => (s.1, none))
        (.goto fun _ => .inr .prepareRow))
      (.load (fun s => (s.1, none)) (.goto fun _ => .inr .reverseOutput)))

variable {ρ : Type} [Fintype ρ]

/-- Actual statements for the table loop. No unbounded natural number is
stored in the state or evaluated by a state-update function. -/
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

/-- The complete finite program. The vertex count is supplied on a tape,
while the small table and all finite control types depend only on fixed `d`. -/
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

/-- Every transition of an actual row run embeds with its original cost,
preserving the position and both extra tapes, including its return jump. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

namespace MaxCutGames.Foundations.Complexity.MachineAlphabetTransport

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

end MaxCutGames.Foundations.Complexity.MachineAlphabetTransport

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

abbrev Tape := MachineExpanderTable.Tape ⊕ ExtraTape
abbrev Alphabet : Tape → Type :=
  MachineEmbedding.Alphabet MachineExpanderTable.Alphabet (fun _ : ExtraTape => Bool)
abbrev BoolAlphabet (_ : Tape) := Bool

/-- All physical tapes contain Booleans. This equality changes the static
type presentation only; no runtime symbol conversion is performed. -/
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

/-- Uniform-alphabet presentation of the actual outer code. All arithmetic
parameters here are fixed program constants; runtime sizes are scanned. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-! Static, pointwise Boolean presentation of the actual family tape alphabet.
Every conversion below is an identity on symbols and has no machine runtime. -/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

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

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-!
# Actual family-table installation and counter cleanup

Checked physical drain and transfer loops are placed in the family program
through its finite register equivalence. Alphabet equality transports their
actual traces back to the dependent alphabet of the full family machine.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

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

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.AlphabetTable

/-- Every tape except the accumulator is literally retained. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Actual lookup and reversal phases of the expander row program

The Boolean phase selector chooses the first or second occurrence of the same
preserving lookup. The selected word is proved to be the actual stored reverse
index of the supplied graph row. All execution facts follow from the concrete
program statements; no phase execution is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open MachineComposition

variable {K Λ ρ : Type} [DecidableEq K] [Fintype ρ]

/-- The exact cleaned tape state produced by either lookup. -/
def lookupResultTapes (ports : Tape → K) (base : K → List Bool)
    (value : Nat) (indexSuffix : List Bool) : K → List Bool :=
  MachinePreservingLookup.initialTapes (ports ∘ lookupTape) base 0 indexSuffix []
    (encodeWord value ++ base (ports .lookupOutput))

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

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

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderRowFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete data and tape frames for an actual expander-row computation

Only the five actual row inputs are stored. Every address, table return and
finite control value below is computed from those inputs. The thirteen tape
frames use the existing phase-output functions. These are data identities and
size bounds, not assumed machine executions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

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

/-- Complete explicit tape contents; all three scratch roles omitted here are empty. -/
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

/-! Direct input facts for the individual checked phase traces. -/

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

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

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

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderTableEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact row enumeration and accumulator contents for an expander-table step

The outer loop enumerates original vertices, and the inner loop enumerates
cloud/port positions in increasing mixed-radix order. The resulting list is
the actual next table's stored rotation-word list. Prefix and reverse-encoding
identities describe data accumulated by a row loop; they assert no runtime.
-/

namespace MaxCutGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open MaxCutGames.Foundations.Complexity

variable {v d : Nat}

/-- Input position in the actual next table, with port varying fastest. -/
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

/-- The number emitted by the checked pure row evaluator. -/
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

/-- Associativity of the three stored mixed-radix coordinates. -/
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

/-- Complete equality with the actual materialized next-table word order. -/
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

/-- This is exactly the accumulator update performed after each emitted row. -/
def accumulate (values : List Nat) (initial : List Bool) : List Bool :=
  values.foldl (fun accumulator value => (encodeWord value).reverse ++ accumulator) initial

end MaxCutGames.Foundations.PCP.ExpanderTableEnumeration

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderTableRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

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

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

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

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

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

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

def timeCoefficient (d : Nat) : Nat :=
  rowFactor d * (rowFactor d + 1) + 82 * rowFactor d + 5

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (timeCoefficient d) * (Polynomial.X + 1) ^ 2

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

/-- The six nonempty tape roles that may occur between expansion phases. -/
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

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds

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

end MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

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

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

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

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

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

/-- The only shared tape is the level: the first phase writes the exact word
that the second phase's unary guard consumes. -/
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

/-- The family retains the completed ceiling machine's two finite registers. -/
def familySource (H : SmallTable) : MachineExpanderFamily.Label fixedDegree →
    TM2.Stmt MachineExpanderFamily.BoolAlphabet
      (MachineExpanderFamily.Label fixedDegree) (State ρ) :=
  MachineStateFrame.frameProgram (τ := Bool × Option Bool)
    (MachineExpanderFamily.boolView MachineExpanderFamily.baseDegree_positive H
      MachineExpanderFamily.baseDegree_cloud_gt_one)

/-- The ceiling program preserves the family state as its ambient component. -/
def ceilingSource : MachineCeilingPower.Label →
    TM2.Stmt MachineCeilingPower.Alphabet MachineCeilingPower.Label (State ρ) :=
  MachineStateEquiv.program (ceilingStates ρ)
    (MachineCeilingPower.program PCP.ExpanderFamily.growth)

/-- Actual composition on shared Boolean tapes. No runtime bridge operation
is required, because both programs use the same physical level tape. -/
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

/-- Initial state for an arbitrary preserved family-state component. -/
def initialState (state : MachineExpanderFamily.State ρ fixedDegree)
    (register : Option Bool) : State ρ := (state, (false, register))

def finalState (H : SmallTable) (state : MachineExpanderFamily.State ρ fixedDegree) : State ρ :=
  (MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H
    (MachineExpanderFamily.caller state), (false, none))

/-- Only the unary request is initially present. -/
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

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

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

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamily

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePaddedExpanderFamilyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords

def outputWord
    (H : Table (cloudSize PCP.Expanders.baseDegree) PCP.Expanders.baseDegree) (k : Nat) :
    List Bool :=
  encodeWords (rotationWords (family H (PCP.PreprocessingLevels.boundedLevel k)))

end MaxCutGames.Foundations.Complexity.MachinePaddedExpanderFamilyBounds

/-!
# Actual requested-size to expander-table computation

One finite program physically computes the padding level and then constructs
the complete corresponding rotation table. The level output of the first
phase is the input tape of the second phase. The actual execution preserves
the request, retains the padded size, and has a fixed polynomial time bound
in the unary request length.
-/

/-!
# Materializing a cloud rotor inside the regularization machine

Core tape 4 contains the unary cloud size and core tape 7 receives the complete
forward rotor table. The actual family computation runs on private tapes;
three retained unary words are then physically drained. All other core tapes
are preserved and all private tapes are empty on return.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularFamily

open Turing MachineComposition
open MachineCloudPadding

abbrev NativeTape := MachinePaddedExpanderFamily.Tape
abbrev Tape := CoreTape ⊕ NativeTape
abbrev SmallTable := MachinePaddedExpanderFamily.SmallTable
abbrev FamilyState := MachineExpanderFamily.State Unit MachinePaddedExpanderFamily.fixedDegree
abbrev State := (FamilyState × Bool) × Option Bool

def inputNative : NativeTape := .inr .input
def outputNative : NativeTape := .inl MachineExpanderFamily.tableTape
def powerNative : NativeTape := .inr .power
def sizeNative : NativeTape := .inl (.inr .currentSize)
def levelNative : NativeTape := .inl (.inr .remainingLevel)

def powerTape : Tape := .inr powerNative
def sizeTape : Tape := .inr sizeNative
def levelTape : Tape := .inr levelNative

def familyView : Tape → Option NativeTape
  | .inl i => if i = 4 then some inputNative else if i = 7 then some outputNative else none
  | .inr t => if t = inputNative then none else if t = outputNative then none else some t

def stateEquiv : MachinePaddedExpanderFamily.State Unit ≃ State :=
  (Equiv.prodAssoc FamilyState Bool (Option Bool)).symm

def seedState (H : SmallTable) : FamilyState :=
  MachineExpanderFamily.initialState MachineExpanderFamily.baseDegree_positive H ()

def readyState (H : SmallTable) : State := ((seedState H, false), none)

def frame (core : CoreTape → List Bool) : Tape → List Bool
  | .inl i => core i
  | .inr _ => []

def rotor (H : SmallTable) (k : Nat) : List Bool :=
  MachinePaddedExpanderFamilyBounds.outputWord H k

def resultCore (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    CoreTape → List Bool := Function.update core 7 (rotor H k)

def working (core : CoreTape → List Bool) (power size level : List Bool) : Tape → List Bool
  | .inl i => core i
  | .inr t => if t = powerNative then power
      else if t = sizeNative then size else if t = levelNative then level else []

@[simp] theorem working_power (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l powerTape = p := by simp [working, powerTape]

@[simp] theorem working_size (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l sizeTape = s := by
  simp [working, sizeTape, powerNative, sizeNative]

@[simp] theorem working_level (core : CoreTape → List Bool) (p s l : List Bool) :
    working core p s l levelTape = l := by
  simp [working, levelTape, powerNative, sizeNative, levelNative]

@[simp] theorem working_empty (core : CoreTape → List Bool) :
    working core [] [] [] = frame core := by
  funext t; cases t <;> simp [working, frame]

@[simp] theorem source_initial_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.initialState (seedState H) none) =
      readyState H := rfl

@[simp] theorem source_final_state (H : SmallTable) :
    stateEquiv (MachinePaddedExpanderFamily.finalState H (seedState H)) =
      readyState H := by
  simp [stateEquiv, MachinePaddedExpanderFamily.finalState, readyState, seedState]

@[simp] theorem result_output (H : SmallTable) (k : Nat) (core : CoreTape → List Bool) :
    frame (resultCore H k core) (.inl 7) = rotor H k := by simp [frame, resultCore]

@[simp] theorem result_private_empty (H : SmallTable) (k : Nat)
    (core : CoreTape → List Bool) (t : NativeTape) :
    frame (resultCore H k core) (.inr t) = [] := rfl

end MaxCutGames.Foundations.Complexity.MachineRegularFamily

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

@[simp] theorem tapes_left (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 0) = left := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_right (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 1) = right := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedLeft (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 2) = savedLeft := by
  simp [tapes, slots.injective.eq_iff]

@[simp] theorem tapes_savedRight (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight : List Bool) :
    tapes slots base left right savedLeft savedRight (slots 3) = savedRight := by
  simp [tapes]

@[simp] theorem update_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacement : List Bool) (i : Fin 4) :
    Function.update (tapes slots base left right savedLeft savedRight) (slots i) replacement =
      tapes slots base (if i = 0 then replacement else left)
        (if i = 1 then replacement else right) (if i = 2 then replacement else savedLeft)
        (if i = 3 then replacement else savedRight) := by
  fin_cases i <;> funext k
  all_goals
    by_cases h₀ : k = slots 0
    · subst k; simp [tapes, slots.injective.eq_iff]
    · by_cases h₁ : k = slots 1
      · subst k; simp [tapes, slots.injective.eq_iff]
      · by_cases h₂ : k = slots 2
        · subst k; simp [tapes, slots.injective.eq_iff]
        · by_cases h₃ : k = slots 3
          · subst k; simp [tapes, slots.injective.eq_iff]
          · simp [tapes, h₀, h₁, h₂, h₃]

@[simp] theorem tapes_self (slots : Fin 4 ↪ K) (base : K → List Bool) :
    tapes slots base (base (slots 0)) (base (slots 1)) (base (slots 2)) (base (slots 3)) = base := by
  simp [tapes]

@[simp] theorem transferLeft_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementLeft : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 2) (slots 0)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementLeft =
      tapes slots base replacementLeft right replacementSaved savedRight := by
  simp [Reduction.MachineTransfer.tapesAt]

@[simp] theorem transferRight_tapes (slots : Fin 4 ↪ K) (base : K → List Bool)
    (left right savedLeft savedRight replacementSaved replacementRight : List Bool) :
    Reduction.MachineTransfer.tapesAt (slots 3) (slots 1)
      (tapes slots base left right savedLeft savedRight) replacementSaved replacementRight =
      tapes slots base left replacementRight savedLeft replacementSaved := by
  simp [Reduction.MachineTransfer.tapesAt]

end MaxCutGames.Foundations.Complexity.MachineUnaryLessAt

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RoundGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Size of the actual fixed amplification round

All constants below depend only on the fixed port alphabet and walk length.
The round itself is the checked preprocessing, powering, and alphabet graph
construction in `AmplificationRound`; no second graph constructor is introduced.
Closed constants are kept symbolic rather than evaluated.
-/

/-!
The actual finite graph iteration used by the mathematical PCP construction.
One fixed, explicitly supplied complete address list is shared by every round.
Each round constructs a new constraint graph. The scalar gap and size are the
actual minimum rejection fraction and actual finite cardinalities of that graph.

The final Boolean formula uses supplied vertex and dart numberings. These
theorems establish the finite objects and their size/gap properties, not a
machine running-time theorem or an independently encoded NP-hardness theorem.
-/

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace MaxCutGames.Foundations.PCP.FinalTableFormula

open Target Complexity

def output (table : GraphTables.Table) : Formula :=
  FinalBooleanVerifier.cnf (FinalCNFPattern.tableGraph table) (Equiv.refl _) (Equiv.refl _)

@[simp] theorem variable_count (table : GraphTables.Table) :
    (output table).«variables» = table.vertices * 6 + table.darts * 36864 :=
  FinalBooleanVerifier.cnf_variable_count _ (Equiv.refl _) (Equiv.refl _)

@[simp] theorem clause_count (table : GraphTables.Table) :
    (output table).clauses.length = table.darts * 40960 :=
  FinalBooleanVerifier.cnf_clause_count _ (Equiv.refl _) (Equiv.refl _)

end MaxCutGames.Foundations.PCP.FinalTableFormula

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineClone100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A finite-state validator for the concrete ordinary-binary formula encoding.
It checks clause and literal framing, canonical name payloads, and the unique
terminal formula marker. The last-digit register starts at true for each name,
so the empty payload is accepted as zero while a nonempty payload must end in
one. Every bit following the terminal formula marker causes rejection.
-/

namespace MaxCutGames.BinaryValidatorMachine

open BinaryEncoding BinaryFormula

theorem finalDigit_true_iff_inline_MachineBinaryValidatorMachine (bits : List Bool) :
    BinaryNameMachine.finalDigit bits (some true) = some true ↔
      BinaryNameMachine.canonical bits = true := by
  cases bits with
  | nil => simp [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
  | cons bit bits =>
      simp only [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
      have hsome : ∀ (ds : List Bool) (b : Bool),
          ∃ last, BinaryNameMachine.finalDigit ds (some b) = some last := by
        intro ds
        induction ds with
        | nil => intro b; exact ⟨b, rfl⟩
        | cons d ds ih => intro b; exact ih d
      obtain ⟨last, hlast⟩ := hsome bits bit
      rw [hlast]
      simp

theorem run_name (slot : Fin 3) (name : Nat) (rest : List Bool) :
    run (.name slot true) (nameBits name ++ rest) = run (afterName slot) rest := by
  apply run_frame
  exact (finalDigit_true_iff_inline_MachineBinaryValidatorMachine name.bits).mpr (BinaryParsing.canonical_nat_bits name)

theorem run_literal (slot : Fin 3) (literal : Literal) (rest : List Bool) :
    run (.sign slot) (literalBits literal ++ rest) = run (afterName slot) rest := by
  simpa only [literalBits, List.cons_append, run, nextMode] using
    run_name slot literal.name rest

theorem run_clause (clause : Clause) (rest : List Bool) :
    run (.sign 0) (clauseBits clause ++ rest) = run .clause rest := by
  simp [clauseBits, List.append_assoc, run_literal, afterName]

theorem run_clauses (clauses : List Clause) : run .clause (clausesBits clauses) = .done := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      change run (.sign 0) (clauseBits clause ++ clausesBits clauses) = .done
      rw [run_clause, ih]

theorem run_formula (formula : Formula) : run .clause (formulaBits formula) = .done :=
  run_clauses formula.clauses

theorem name_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.name slot true) input = .done) :
    ∃ name rest, input = nameBits name ++ rest ∧ run (afterName slot) rest = .done := by
  obtain ⟨bits, rest, hinput, hvalid, hrest⟩ := frame_inverse slot true input accepted
  have hcanonical := (finalDigit_true_iff_inline_MachineBinaryValidatorMachine bits).mp hvalid
  have hbits := (BinaryParsing.canonical_iff bits).mp hcanonical
  refine ⟨bitsValue bits, rest, ?_, hrest⟩
  simpa only [nameBits, hbits] using hinput

theorem literal_inverse (slot : Fin 3) (input : List Bool)
    (accepted : run (.sign slot) input = .done) :
    ∃ literal rest, input = literalBits literal ++ rest ∧ run (afterName slot) rest = .done := by
  cases input with
  | nil => simp [run] at accepted
  | cons sign input =>
      have haccepted : run (.name slot true) input = .done := accepted
      obtain ⟨name, rest, hinput, hrest⟩ := name_inverse slot input haccepted
      refine ⟨⟨name, sign⟩, rest, ?_, hrest⟩
      simp [literalBits, hinput]

theorem clause_inverse (input : List Bool) (accepted : run (.sign 0) input = .done) :
    ∃ clause rest, input = clauseBits clause ++ rest ∧ run .clause rest = .done := by
  obtain ⟨a, afterA, hA, acceptedA⟩ := literal_inverse 0 input accepted
  have hacceptedA : run (.sign 1) afterA = .done := by
    simpa [afterName] using acceptedA
  obtain ⟨b, afterB, hB, acceptedB⟩ := literal_inverse 1 afterA hacceptedA
  have hacceptedB : run (.sign 2) afterB = .done := by
    simpa [afterName] using acceptedB
  obtain ⟨c, rest, hC, acceptedC⟩ := literal_inverse 2 afterB hacceptedB
  have hrest : run .clause rest = .done := by simpa [afterName] using acceptedC
  refine ⟨#v[a, b, c], rest, ?_, hrest⟩
  simp [clauseBits, hA, hB, hC, List.append_assoc]

theorem clauses_inverse_aux_inline_MachineBinaryValidatorMachine (fuel : Nat) (input : List Bool)
    (enough : input.length < fuel) (accepted : run .clause input = .done) :
    ∃ clauses, input = clausesBits clauses := by
  induction fuel generalizing input with
  | zero => omega
  | succ fuel ih =>
      cases input with
      | nil => simp [run] at accepted
      | cons flag input =>
          cases flag with
          | false =>
              have hdone : run .done input = .done := accepted
              have hempty := (run_done_iff input).mp hdone
              subst input
              exact ⟨[], rfl⟩
          | true =>
              have haccepted : run (.sign 0) input = .done := accepted
              obtain ⟨clause, rest, hinput, hrest⟩ := clause_inverse input haccepted
              have hlength := congrArg List.length hinput
              simp only [List.length_append] at hlength
              have henough : rest.length < fuel := by
                simp only [List.length_cons] at enough
                omega
              obtain ⟨clauses, hclauses⟩ := ih rest henough hrest
              refine ⟨clause :: clauses, ?_⟩
              simp [clausesBits, hinput, hclauses]

/-- Exact language recognition, including rejection of incomplete, padded,
or trailing input. -/
theorem run_clause_iff (input : List Bool) :
    run .clause input = .done ↔ ∃ formula, input = formulaBits formula := by
  constructor
  · intro accepted
    obtain ⟨clauses, hclauses⟩ :=
      clauses_inverse_aux_inline_MachineBinaryValidatorMachine (input.length + 1) input (by omega) accepted
    exact ⟨⟨clauses⟩, hclauses⟩
  · rintro ⟨formula, rfl⟩
    exact run_formula formula

/-! ## Concrete finite-stack execution -/

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition

end MaxCutGames.BinaryValidatorMachine

/-!
Total raw-input preprocessing for the ordinary binary formula codec. The
machine copies each input bit onto a reverse stack while running the finite
validator. Accepted words are restored verbatim; rejected words are drained
and replaced by the fixed contradictory formula. All three stack alphabets
and all control/register types are finite.
-/

namespace MaxCutGames.BinaryTotalInputMachine

open Turing
open MaxCutGames.Foundations.Complexity
open MachineComposition
open MaxCutGames.Reduction.MachineTransfer
open MaxCutGames.Reduction.MachineSubstitution
open BinaryValidatorMachine (Mode nextMode run)

def rejectedWord : List Bool := BinaryEncoding.formulaBits BinaryLanguage.rejectBinary

/-- Stack zero is the input, one the output, and two the reversed input.
Branches inspect only the finite validator state and the popped symbol. -/
def instruction : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push 2 (fun state => state.2.getD false)
            (.load (fun state => (nextMode state.1 (state.2.getD false), none))
              (.goto fun _ => .scan)))
          (.branch (fun state => decide (state.1 = .done))
            (.load (fun _ => (.clause, none)) (.goto fun _ => .restore))
            (.load (fun _ => (.clause, none)) (.goto fun _ => .drain))))
  | .restore => loopAt 2 1 id false .restore none
  | .drain => MachineDrain.drain 2 .drain (some .rejectOutput)
  | .rejectOutput => pushWord 1 rejectedWord.reverse .halt

abbrev machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (.clause, none)
  m := instruction

def cfg (label : Option Label) (input output saved : List Bool) (mode : Mode := .clause)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input output saved⟩

theorem step_scan_empty (output saved : List Bool) (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) [] output saved mode register) =
      some (cfg (some (afterScan mode)) [] output saved) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  by_cases accepted : mode = .done <;>
    simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryTotalInputMachine, afterScan, accepted] <;> rfl

theorem step_scan_cons (bit : Bool) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) (bit :: input) output saved mode register) =
      some (cfg (some .scan) input output (bit :: saved) (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input_inline_MachineBinaryTotalInputMachine, update_saved_inline_MachineBinaryTotalInputMachine]
  rfl

/-- The finite DFA reads every bit, including all bits in its rejection sink.
The trace also records the physical reversed copy needed by the second phase. -/
theorem scanTrace (input output saved : List Bool) (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .scan) input output saved mode register)) =
      some (cfg (some (afterScan (run mode input))) [] output (input.reverse ++ saved)) := by
  induction input generalizing saved mode register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run, List.reverse_nil, List.nil_append] using
          step_scan_empty output saved mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: saved) (nextMode mode bit) none

theorem restoreTrace (saved output : List Bool) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .restore) [] output saved .clause register)) =
      some (cfg none [] (saved.reverse ++ output) []) := by
  change (nextAt (1 : Fin 3) instruction)^[saved.length + 1]
    (some ⟨some .restore, (Mode.clause, register), tapes [] output saved⟩) =
    some ⟨none, (Mode.clause, none), tapes [] (saved.reverse ++ output) []⟩
  have trace := transferAt_steps (2 : Fin 3) 1 (by decide) id false .restore none
    instruction rfl (tapes [] [] []) saved output Mode.clause register
  simpa only [tapesAt, update_saved_inline_MachineBinaryTotalInputMachine, update_output_inline_MachineBinaryTotalInputMachine,
    List.map_id_fun, id_eq] using trace

theorem drainTrace (saved output : List Bool) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .drain) [] output saved .clause register)) =
      some (cfg (some .rejectOutput) [] output []) := by
  change (advance (TM2.step instruction))^[saved.length + 1]
    (some ⟨some .drain, (Mode.clause, register), tapes [] output saved⟩) =
    some ⟨some .rejectOutput, (Mode.clause, none), tapes [] output []⟩
  have trace := MachineDrain.drainTrace (2 : Fin 3) .drain (some .rejectOutput)
    instruction rfl (tapes [] output []) saved Mode.clause register
  simpa only [update_saved_inline_MachineBinaryTotalInputMachine] using trace

theorem step_rejectOutput (output : List Bool) :
    machine.step (cfg (some .rejectOutput) [] output []) =
      some (cfg none [] (rejectedWord ++ output) []) := by
  change some (TM2.stepAux
    (pushWord (Γ := Alphabet) (Λ := Label) (σ := State)
      (1 : Fin 3) rejectedWord.reverse .halt) _ _) = _
  rw [stepAux_pushWord]
  simp only [cfg, List.reverse_reverse, tapes_output, update_output_inline_MachineBinaryTotalInputMachine, TM2.stepAux]
  rfl

theorem acceptedTrace (input : List Bool) (accepted : run .clause input = .done) :
    (advance machine.step)^[2 * input.length + 2]
      (some (cfg (some .scan) input [] [])) = some (cfg none [] input []) := by
  have first := scanTrace input [] [] .clause none
  simp only [afterScan, accepted, ↓reduceIte, List.append_nil] at first
  have second := restoreTrace input.reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at second
  have time : 2 * input.length + 2 = (input.length + 1) + (input.length + 1) := by omega
  rw [time]
  exact joinTrace_inline_MachineBinaryTotalInputMachine first second

theorem rejectedTrace (input : List Bool) (rejected : run .clause input ≠ .done) :
    (advance machine.step)^[2 * input.length + 3]
      (some (cfg (some .scan) input [] [])) = some (cfg none [] rejectedWord []) := by
  have first := scanTrace input [] [] .clause none
  simp only [afterScan, rejected, ↓reduceIte, List.append_nil] at first
  have second := drainTrace input.reverse [] none
  simp only [List.length_reverse] at second
  have third : (advance machine.step)^[1]
      (some (cfg (some .rejectOutput) [] [] [])) = some (cfg none [] rejectedWord []) := by
    simpa only [Function.iterate_one, advance_some, List.append_nil] using
      step_rejectOutput []
  have time : 2 * input.length + 3 = (input.length + 1) + (input.length + 1) + 1 := by omega
  rw [time]
  exact joinTrace_inline_MachineBinaryTotalInputMachine (joinTrace_inline_MachineBinaryTotalInputMachine first second) third

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .scan) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] output [] := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Full correspondence on every raw word, with no validity premise. -/
theorem totalTrace (input : List Bool) :
    (advance machine.step)^[steps input] (some (initList machine input)) =
      some (haltList machine (BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input))) := by
  rw [initList_eq, haltList_eq]
  cases parsed : BinaryEncoding.decodeFormula input with
  | none =>
      have rejected : run .clause input ≠ .done := by
        intro accepted
        obtain ⟨formula, encoded⟩ := (BinaryValidatorMachine.run_clause_iff input).mp accepted
        have roundtrip := BinaryEncoding.decodeFormula_encoded formula
        rw [← encoded, parsed] at roundtrip
        cases roundtrip
      simpa only [steps, rejected, ↓reduceIte, BinaryLanguage.totalParsed, parsed,
        Option.getD_none, rejectedWord] using rejectedTrace input rejected
  | some formula =>
      have encoded := BinaryParsing.decodeFormula_sound input formula parsed
      have accepted := (BinaryValidatorMachine.run_clause_iff input).mpr ⟨formula, encoded⟩
      simp only [steps, accepted, ↓reduceIte, BinaryLanguage.totalParsed, parsed,
        Option.getD_some]
      rw [← encoded]
      exact acceptedTrace input accepted

def outputsInTime (input : List Bool) :
    TM2OutputsInTime machine input
      (some (BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input)))
      (2 * input.length + 3) where
  steps := steps input
  evals_in_steps := totalTrace input
  steps_le_m := steps_le input

/-- The certificate contains the displayed total machine and its linear trace;
it assumes no execution, parser-cost, or malformed-input premise. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime (id : List Bool → List Bool) BinaryEncoding.formulaBits
      BinaryLanguage.totalParsed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 3
  outputsFun input := by
    change TM2OutputsInTime machine (input.map id)
      (some ((BinaryEncoding.formulaBits (BinaryLanguage.totalParsed input)).map id))
      ((2 * Polynomial.X + 3 : Polynomial Nat).eval input.length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_ofNat] using outputsInTime input

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

theorem computation_finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computableInPolyTime.tm :=
  machine_finiteAlphabet

end MaxCutGames.BinaryTotalInputMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineBinaryInputReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The complete ordinary-binary input bridge. Arbitrary raw input bits are first
validated and retained, or replaced by a fixed contradictory encoded formula.
The checked occurrence-index renamer then emits the inherited dense 3CNF
codec. Both stages and their physical handoff have actual polynomial-time
finite-alphabet machine certificates.

This is a bridge for the explicit ordinary binary 3SAT language. It is not the
PCP construction, a proof of that construction's runtime, or an NP-hardness
assertion about the eventual 2-to-1 target.
-/

namespace MaxCutGames.BinaryInputReduction

open Turing MaxCutGames.Foundations.Complexity

/-- The actual sequential machine handles every bitstring, including malformed
and noncanonical encodings, and outputs the fixed dense formula serialization. -/
noncomputable def computation :
    TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits BinaryLanguage.totalRename := by
  change TM2ComputableInPolyTime (id : List Bool → List Bool) formulaBits
    (fun input => BinaryOccurrenceRename.renamed (BinaryLanguage.totalParsed input))
  exact MachineSequential.composeBits BinaryTotalInputMachine.computableInPolyTime
    BinaryRenameMachine.computableInPolyTime

end MaxCutGames.BinaryInputReduction

end OAI
end


