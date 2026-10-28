-- Prove2me | Definitions.Def_OAIQ087A010
-- name    : OAIQ087A010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:22:10.700536+00:00
-- url     : https://prove2.me/theorems/116ed398-212d-4798-a301-c47467781cc8
-- title:
--   Definitions bundle OAIQ087A010 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 386 declarations of OpenAI's Lean: 155 definitions, 4 inductive types or structures, 7 instances and 220 theorems. The definitions and types are `OAI.MaxCutGames.Explicit.MachineSubdivisionHeaders.resultTapes`, `OAI.MaxCutGames.Explicit.MachineSubdivisionInit.frame`, `OAI.MaxCutGames.Explicit.MachineUniformHeaders.afterAlphabet`, `OAI.MaxCutGames.Explicit.MachineUniformHeaders.afterVertices`, `OAI.MaxCutGames.Explicit.MachineUniformHeaders.resultTapes`, `OAI.MaxCutGames.Explicit.MachineUniformProgram.Label`, `OAI.MaxCutGames.Explicit.MachineUniformProgram.State`, `OAI.MaxCutGames.Explicit.MachineUniformProgram.emitEntry`, `OAI.MaxCutGames.Explicit.MachineUniformProgram.headerNext`, `OAI.MaxCutGames.Explicit.MachineUniformProgram.initialState`, `OAI.MaxCutGames.Explicit.MachineUniformProgram.tokens`, `OAI.MaxCutGames.Explicit.MachineUniformRun.afterEmit`, `OAI.MaxCutGames.Explicit.MachineUniformRun.afterScale`, `OAI.MaxCutGames.Explicit.MachineUniformRun.outputBits`, `OAI.MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program.Label`, `OAI.MaxCutGames.Foundations.Complexity.MachineAppendAt.appendTapes`, `OAI.MaxCutGames.Foundations.Complexity.MachineAppendAt.firstTapes_inline_MachineAppendAt`, `OAI.MaxCutGames.Foundations.Complexity.MachineAppendAt.secondTapes_inline_MachineAppendAt`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.Label`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.cleanupEntry`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.cleanupLabel`, `OAI.MaxCutGames.Foundations.Complexity.MachineCanonicalOutput.resetLabel`, `OAI.MaxCutGames.Foundations.Complexity.MachineCeilingPower.Label.enumList`, `OAI.MaxCutGames.Foundations.Complexity.MachineCeilingPower.Tape.enumList`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.Alphabet`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.Label`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.Placement.configuration`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.Placement.label`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.countTape`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.postTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.powerTape`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.subtractLoop`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPadding.timePolynomial`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.Label`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.cycleBudget`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudPrefix.timePolynomial`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudSelect.BaseTape`, `OAI.MaxCutGames.Foundations.Complexity.MachineCloudSelect.Tape`, `OAI.MaxCutGames.Foundations.Complexity.MachineControl.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineDrainMany.haltTapes` and 119 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Estimates_Basic`, `MaxCut_Games_Basic`, `MaxCut_Games_Basic2`, `MaxCut_Games_LabelBound`, `MaxCut_Games_Reindexing`, `MaxCut_Games_TranslationTarget`, `MaxCut_Games_UpperBound`, `MaxCut_Machines_GraphCounterFinish`, `MaxCut_Machines_Input`, `MaxCut_Machines_Machine`, `MaxCut_Machines_Machine2`, `MaxCut_Machines_MachineCanonicalOutput`, `MaxCut_Machines_MachineCloudCount`, `MaxCut_Machines_MachineCloudPadding`, `MaxCut_Machines_MachineCloudPrefix`, `MaxCut_Machines_MachineCloudSelect`, `MaxCut_Machines_MachineCopy`, `MaxCut_Machines_MachineDummyRows`, `MaxCut_Machines_MachineExpanderTableProgram`, `MaxCut_Machines_MachineExpanderTableRows`, `MaxCut_Machines_MachineFieldProfile`, `MaxCut_Machines_MachineFiniteTable`, `MaxCut_Machines_MachineFixedDivMod`, `MaxCut_Machines_MachineInitialHeaders`, `MaxCut_Machines_MachineLazyTableRuntime`, `MaxCut_Machines_MachinePaddedExpanderFamilyBounds`, `MaxCut_Machines_MachinePaddedOverlay`, `MaxCut_Machines_MachinePortReindex`, `MaxCut_Machines_MachineRegisterEmit`, `MaxCut_Machines_MachineRegularLift`, `MaxCut_Machines_MachineRegularMetadata`, `MaxCut_Machines_MachineRegularOwnerProgram`, `MaxCut_Machines_MachineRegularTableRuntime`, `MaxCut_Machines_MachineRegularTableTrace`, `MaxCut_Machines_MachineRegularVertexBlock`, `MaxCut_Machines_MachineStateFrame`, `MaxCut_Machines_MachineSubdivisionDynamicRows`, `MaxCut_Machines_MachineUnaryAffine`, `MaxCut_Machines_PoweringMachineLoop`, `MaxCut_Machines_PoweringMachineRotor`, `MaxCut_Machines_PoweringMachineVertex`, `MaxCut_Machines_PoweringRuntimeBudget`, `MaxCut_Machines_RawInitialMachineCleanup`, `MaxCut_Machines_RawInitialMachineModel`, `MaxCut_Machines_Runtime2`, `MaxCut_Machines_RuntimeSpace`, `MaxCut_PCP_AnalyticCheeger`, `MaxCut_PCP_DistributionMaps`, `MaxCut_PCP_ExpanderFamily`, `MaxCut_PCP_Folding`, `MaxCut_PCP_Generator`, `MaxCut_PCP_KernelIteration`, `MaxCut_PCP_Overlap`, `MaxCut_PCP_PortTables`, `MaxCut_PCP_PoweringOpinionTables`, `MaxCut_PCP_PoweringRowData`, `MaxCut_PCP_PoweringRowHeaderSemantics`, `MaxCut_PCP_PreprocessingLazyWords`, `MaxCut_PCP_PreprocessingOverlayWords`, `MaxCut_PCP_PreprocessingPaddingOffsets`, `MaxCut_PCP_PreprocessingPaddingWords`, `MaxCut_PCP_PreprocessingRegularBounds`, `MaxCut_PCP_PreprocessingRegularLoopWords`, `MaxCut_PCP_PreprocessingRegularSoundness`, `MaxCut_PCP_PreprocessingRegularTables`, `MaxCut_PCP_ProductCollisionBounds`, `MaxCut_PCP_RawInitialTables`, `MaxCut_PCP_Rounding`, `MaxCut_PCP_SpectralCut`.
--
--   **Imports.** It imports the bundles `OAIQ087A000`, `OAIQ087A001`, `OAIQ087A002`, `OAIQ087A003` and `OAIQ087A004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A017`, `OAIQ087A018` and `OAIQ087A019`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A000
import Definitions.Def_OAIQ087A001
import Definitions.Def_OAIQ087A002
import Definitions.Def_OAIQ087A003
import Definitions.Def_OAIQ087A004

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Machine2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity

def formulaEncoding : Computability.Encoding Target.Formula Bool where
  encode := formulaBits
  decode := decodeFormulaBits
  decode_encode := decodeFormulaBits_encoded

open Target

end MaxCutGames.Foundations.Complexity

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_TranslationTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.UniformTarget

open MaxCutGames.Foundations Target Complexity
open MaxCutGames.Integration
open MachineUniformCopyOrder

theorem encode_copies (C : Nat) (words : List Nat) :
    encodeWords (copyMajor C words) = copyMajor C (encodeWords words) := by
  induction C with
  | zero => rfl
  | succ C ih =>
    simpa only [copyMajor, List.replicate_succ, List.flatten_cons,
      encodeWords_append] using congrArg (fun xs => encodeWords words ++ xs) ih

end MaxCutGames.Explicit.UniformTarget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A certified machine for fixed symbol substitution

For a fixed table `emit : Bool → List Bool`, this actual finite TM2 machine
produces `(input.flatMap emit).reverse` in exactly `2 * input.length + 1`
transitions. It has one input-pop transition and one literal-emission transition
per input symbol, followed by the final empty pop. Literal emission is a fixed
finite statement; its maximum number of pushes depends only on `emit`.

This is a machine primitive, not a runtime theorem for the Unique Games reduction.
-/

/-! Static renaming of labels and finite internal states. This does not execute
a data-copying phase and preserves every actual transition exactly. -/

namespace MaxCutGames.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

variable [DecidableEq K]

def program (labels : Λ ≃ Λ') (states : σ ≃ σ') (source : Λ → Stmt Γ Λ σ) :
    Λ' → Stmt Γ Λ' σ' := fun l => statement labels states (source (labels.symm l))

/-- The renamed program is conjugate to the original transition function,
including the halted configuration. -/
theorem step_simulation (labels : Λ ≃ Λ') (states : σ ≃ σ')
    (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program labels states source) (configuration labels states c) =
      (step source c).map (configuration labels states) := by
  cases c with
  | mk l state tapes =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (statement labels states (source (labels.symm (labels l))))
        (states state) tapes) = _
      rw [Equiv.symm_apply_apply, stepAux_simulation]
      rfl

end MaxCutGames.Foundations.Complexity.MachineControl

/-! Static exchange of the first two groups of stacks. Symbol types and stack
contents are retained exactly; no machine transition is spent on this layout
change. This aligns the two component machines in sequential composition. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Machine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complete-stack cleanup, with an arbitrary continuation. Each symbol
costs one transition and the empty-stack branch costs one final transition. -/

/-! Static concatenation of finitely many concrete subroutines on common
tapes. The labels are a finite disjoint sum; no runtime instruction counter
or list is placed in the machine state. The simulation theorem composes the
actual local traces with exactly their summed transition counts. -/

/-!
# Actual cleanup of a finite list of work tapes

Each list position supplies one fixed drain label. The finite-sequence theorem
composes the checked physical drains; neither the list nor a runtime tape index
is stored in the register. Repeated tape names are allowed. The cleanup bound
uses the lengths before cleanup, since draining can only shorten a tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineDrainMany

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

/-- The tape component of the actual halted configuration: only output remains. -/
def haltTapes (output : K) (word : List Bool) : Tapes K :=
  fun k => if k = output then word else []

theorem finalTapes_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K)
    (base : Tapes K) :
    finalTapes (workTapes enumeration output) base = haltTapes output (base output) := by
  funext k
  rw [finalTapes_apply]
  by_cases h : k = output
  · subst k
    simp [haltTapes]
  · simp [haltTapes, h]

end MaxCutGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineUnaryAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A real finite program for uniform whole-instance copying. It reads three
headers, physically multiplies the occurrence count by the fixed constant,
copies the header-free body the same fixed number of times, and clears all
working tapes. No input-dependent data are placed in finite control. -/

namespace MaxCutGames.Explicit.MachineUniformProgram

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad

abbrev State := MachineFieldTemplate.State Unit

def initialState : State := (((), ()), none)

def tokens (C : Nat) : List (MachineFieldTemplate.Token 4) :=
  [.copy 0, .copy 1, .copy 2] ++ List.replicate C (.copy 3)

inductive Label (C : Nat)
  | headerStart (i : Fin 3)
  | headerRead (i : Fin 3)
  | scale (phase : Fin 3)
  | emit (label : MachineFieldTemplate.Label (tokens C).length)
  | finishStart
  | finish (label : SourceRuntimeFinish.Label clearKeys)
  deriving DecidableEq, Fintype

def headerNext {C : Nat} (i : Fin 3) : Label C :=
  if h : i.val + 1 < 3 then .headerStart ⟨i.val + 1, h⟩ else .scale 0

def emitEntry (C : Nat) : Label C :=
  .emit (MachineFieldTemplate.startAt (tokens C).length 0)

end MaxCutGames.Explicit.MachineUniformProgram

/-! Exact execution of the three input-header reads of uniform copying. -/

namespace MaxCutGames.Explicit.MachineUniformHeaders

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineUniformProgram

def afterVertices (n : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n else []

def afterAlphabet (n q : Nat) (rest : List Bool) : Tape → List Bool :=
  fun k => if k = .input then rest else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q else []

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabet then encodeWord q
    else if k = .occurrences then encodeWord Q else []

theorem first_result (n : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .vertices
      (inputTapes (encodeWord n ++ rest)) rest
      (encodeWord n ++ inputTapes (encodeWord n ++ rest) .vertices) =
      afterVertices n rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, inputTapes, afterVertices]

theorem second_result (n q : Nat) (rest : List Bool) :
    SourceMachine.fieldTapes Tape.input .alphabet
      (afterVertices n (encodeWord q ++ rest)) rest
      (encodeWord q ++ afterVertices n (encodeWord q ++ rest) .alphabet) =
      afterAlphabet n q rest := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterVertices, afterAlphabet]

theorem third_result (n q Q : Nat) (body : List Bool) :
    SourceMachine.fieldTapes Tape.input .occurrences
      (afterAlphabet n q (encodeWord Q ++ body)) body
      (encodeWord Q ++ afterAlphabet n q (encodeWord Q ++ body) .occurrences) =
      resultTapes n q Q body := by
  funext k
  cases k <;> simp [SourceMachine.fieldTapes, afterAlphabet, resultTapes]

end MaxCutGames.Explicit.MachineUniformHeaders

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

namespace MaxCutGames.Foundations.Complexity.MachineRepeat
open Turing

abbrev Symbols (M : FinTM2) := MachineEmbedding.Alphabet M.Γ (fun _ : ExtraTape => M.Γ M.k₀)

def auxProgram (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool) :
    Phase → TM2.Stmt (Symbols M) (Label M) (State M)
  | .parse => .pop (.inl M.k₀) (fun s v => (s.1,v))
      (.branch (fun s => input (s.2.getD (input.symm false)))
        (.push (.inr .counter) (fun _ => input.symm true)
          (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .parse))))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .guard))))
  | .guard => .pop (.inr .counter) (fun s v => (s.1,v))
      (.branch (fun s => s.2.isSome)
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inl M.main)))
        (.load (fun s => (s.1,none)) (.goto (fun _ => .inr .finalToTemp))))
  | .bodyToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₁) (.inr .temporary)
      (fun b => input.symm (output b)) (input.symm false)
      (.inr .bodyToTemp) (some (.inr .tempToBody))
  | .tempToBody => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inl M.k₀)
      id (input.symm false) (.inr .tempToBody) (some (.inr .guard))
  | .finalToTemp => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inl M.k₀) (.inr .temporary)
      id (input.symm false) (.inr .finalToTemp) (some (.inr .tempToOutput))
  | .tempToOutput => Reduction.MachineTransfer.loopAt (Γ := Symbols M) (Λ := Label M) (.inr .temporary) (.inr .output)
      id (input.symm false) (.inr .tempToOutput) none

def inputTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (initList M word).stk (extraTapes M counter [] [])

@[simp] theorem inputTapes_input (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inl M.k₀) = word := by
  simp [inputTapes, initList]

@[simp] theorem inputTapes_counter (M : FinTM2) (word counter : List (M.Γ M.k₀)) :
    inputTapes M word counter (.inr .counter) = counter := rfl

def inputConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),inputTapes M word counter⟩

def temporaryTapes (M : FinTM2) (word counter : List (M.Γ M.k₀)) : ∀k, List (Symbols M k) :=
  MachineEmbedding.tapes (fun _ => []) (extraTapes M counter word [])

def temporaryConfig (M : FinTM2) (phase : Phase) (word counter : List (M.Γ M.k₀)) :
    TM2.Cfg (Symbols M) (Label M) (State M) :=
  ⟨some (.inr phase),(M.initialState,none),temporaryTapes M word counter⟩

theorem inputTapes_update_input_inline_MachineRepeat (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inl M.k₀) replacement =
      inputTapes M replacement counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [inputTapes, initList]
    · simp [inputTapes, initList, h]
  | inr k => simp [inputTapes]

theorem inputTapes_update_counter_inline_MachineRepeat (M : FinTM2)
    (word counter replacement : List (M.Γ M.k₀)) :
    Function.update (inputTapes M word counter) (.inr .counter) replacement =
      inputTapes M word replacement := by
  funext k
  cases k with
  | inl k => simp [inputTapes]
  | inr k => cases k <;> simp [inputTapes, extraTapes]

variable (M : FinTM2) (input : M.Γ M.k₀ ≃ Bool) (output : M.Γ M.k₁ ≃ Bool)

theorem tempToBody_tapes_inline_MachineRepeat (word counter : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inr .temporary) (.inl M.k₀)
      (temporaryTapes M word counter) [] word.reverse = inputTapes M word.reverse counter := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, inputTapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

theorem finalToTemp_tapes_inline_MachineRepeat (word : List (M.Γ M.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols M) (.inl M.k₀) (.inr .temporary)
      (inputTapes M word []) [] word.reverse = temporaryTapes M word.reverse [] := by
  funext k
  cases k with
  | inl k =>
    by_cases h : k = M.k₀
    · subst k; simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, initList, h]
  | inr k =>
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, inputTapes, temporaryTapes, extraTapes]

omit M input output in
/-- Explicit sum form of the actual repeat budget. -/
theorem loopBudget_eq_sum (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat) :
    loopBudget count words budgets =
      (∑ i ∈ Finset.range count, (budgets i + 2*(words (i+1)).length+3)) +
      2*(words count).length+3 := by
  induction count generalizing words budgets with
  | zero => simp [loopBudget]
  | succ count ih =>
    rw [loopBudget, ih, Finset.sum_range_succ']
    simp only [Nat.zero_add]
    omega

omit M input output in
/-- A uniform bound along the executed sequence is enough to bound the actual
repeat runtime. No polynomial growth of an arbitrary iteration is asserted. -/
theorem loopBudget_le (count : Nat) (words : Nat → List Bool) (budgets : Nat → Nat)
    (bodyBound lengthBound : Nat)
    (hb : ∀i, i < count → budgets i ≤ bodyBound)
    (hl : ∀i, i ≤ count → (words i).length ≤ lengthBound) :
    loopBudget count words budgets ≤ count*(bodyBound+2*lengthBound+3)+2*lengthBound+3 := by
  rw [loopBudget_eq_sum]
  have hs : (∑ i ∈ Finset.range count, (budgets i+2*(words (i+1)).length+3)) ≤
      count*(bodyBound+2*lengthBound+3) := by
    calc
      _ ≤ ∑ i ∈ Finset.range count, (bodyBound+2*lengthBound+3) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hbi := hb i hi'
        have hli := hl (i+1) hi'
        omega
      _ = _ := by simp
  have hlast := hl count (le_refl _)
  omega

end MaxCutGames.Foundations.Complexity.MachineRepeat

/-!
Finiteness of every alphabet of the actual machines used by the reduction.
`FinTM2` already bundles finitely many tapes, control labels and register states,
but its alphabet field only requires the input tape alphabet to be finite.
This additional property is preserved by the actual sequential and repetition
constructors; it does not replace or alter their execution certificates.
-/

/-! Whole-instance uniform copying: exact physical header arithmetic, repeated
body emission, actual cleanup, and a polynomial bound in the input codec length. -/

namespace MaxCutGames.Explicit.MachineUniformRun

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations Target
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MachineUniformProgram

def outputBits (C n q Q : Nat) (body : List Bool) : List Bool :=
  encodeWords [n, q, C * Q] ++ MachineUniformCopyOrder.copyMajor C body

def afterScale (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  Function.update (MachineUniformHeaders.resultTapes n q Q body)
    .newOccurrences (encodeWord (C * Q))

def afterEmit (C n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterScale C n q Q body)
    .accumulator (outputBits C n q Q body)

theorem input_length (n q Q : Nat) (body : List Bool) :
    (encodeWords [n, q, Q] ++ body).length = n + q + Q + 3 + body.length := by
  simp [Nat.add_assoc]

end MaxCutGames.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionDynamicRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Four-edge subdivision row emission with a physical permutation-table field.

The program depends only on the fixed identity table. Five saved endpoint words
and the entire final forward permutation table are physical tape contents. In
particular an input-dependent permutation is not inserted into a program label
or literal instruction. The last row is oriented `v → r`; for binary-vector
translations its table equals the inverse table of the original `u → v` edge.
-/

/-!
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

/-! Exact execution of the three input-header reads of subdivision. -/

namespace MaxCutGames.Explicit.MachineSubdivisionHeaders

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineSubdivisionProgram

def resultTapes (n q Q : Nat) (body : List Bool) : Tape → List Bool :=
  fun k => if k = .input then body else if k = .vertices then encodeWord n
    else if k = .alphabetHeader then encodeWord q
    else if k = .occurrences then encodeWord Q else []

end MaxCutGames.Explicit.MachineSubdivisionHeaders

/-! Physical header arithmetic and private-vertex initialization. -/

namespace MaxCutGames.Explicit.MachineSubdivisionInit

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

theorem source_ne_scratch (i : Fin 9) : (initOp i).source ≠ Tape.affineScratch := by
  fin_cases i <;> simp [initOp]

theorem source_ne_destination (i : Fin 9) : (initOp i).source ≠ (initOp i).destination := by
  fin_cases i <;> simp [initOp]

theorem scratch_ne_destination (i : Fin 9) : Tape.affineScratch ≠ (initOp i).destination := by
  fin_cases i <;> simp [initOp]

def frame (n q Q : Nat) (body : List Bool) : Nat → Tape → List Bool
  | 0 => MachineSubdivisionHeaders.resultTapes n q Q body
  | r + 1 => if h : r < 9 then
      Function.update (frame n q Q body r) (initOp ⟨r, h⟩).destination
        (encodeWord (afterValue n Q ⟨r, h⟩))
    else frame n q Q body r

theorem frame_source (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val (initOp i).source = encodeWord (sourceValue n Q i) := by
  fin_cases i <;>
    simp [frame, sourceValue, initOp, MachineSubdivisionHeaders.resultTapes]

theorem frame_scratch (n q Q : Nat) (body : List Bool) (i : Fin 9) :
    frame n q Q body i.val .affineScratch = [] := by
  fin_cases i <;> simp [frame, initOp, MachineSubdivisionHeaders.resultTapes]

theorem sourceValue_le (n Q : Nat) (i : Fin 9) : sourceValue n Q i ≤ n + Q := by
  fin_cases i <;> simp [sourceValue]

end MaxCutGames.Explicit.MachineSubdivisionInit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Folding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit half-table storage, odd folding, and conditioning on the finite
set of satisfying local assignments for Håstad's test. -/

namespace MaxCutGames.Foundations.Hastad.FoldedEquation

open MaxCutGames.Reduction.CloneGap
open scoped BigOperators

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def storedAssignment {i₀ : I} {j₀ : J}
    (tableA : HalfCube i₀ → Bool) (tableB : HalfCube j₀ → Bool) :
    Address i₀ j₀ → Bool := Sum.elim tableA tableB

end MaxCutGames.Foundations.Hastad.FoldedEquation

/-!
Actual equations for clause contexts having no valid local assignment. The
right answer is the constant false bit, represented by two occurrences of one
dummy variable. Those occurrences cancel for every assignment. The remaining
left answer is folded, so its uniform bias is exactly zero.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Basic
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite two-player games with actual joint question distributions.

An answer function receives only its own player's question. In a repeated game,
that question is the entire tuple, so a repeated strategy need not act separately
on coordinates. The predicate may reject invalid answers depending on questions.
All probabilities below are actual finite sums of real weights.
-/

namespace MaxCutGames.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem probability_mono (μ : FiniteDistribution Ω) {event event' : Ω → Bool}
    (h : ∀ x, event x = true → event' x = true) :
    μ.probability event ≤ μ.probability event' := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · simp [hx, h x hx]
  · simp [hx]
    split
    · exact μ.nonnegative x
    · exact le_rfl

end FiniteDistribution

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem expectation_table_eval [DecidableEq Q] (responses : Q → FiniteDistribution A)
    (q₀ : Q) (h : A → ℝ) :
    (table responses).expectation (fun answers => h (answers q₀)) =
      (responses q₀).expectation h := by
  classical
  change (∑ answers : Q → A,
    (∏ q, (responses q).weight (answers q)) * h (answers q₀)) =
      ∑ a, (responses q₀).weight a * h a
  calc
    _ = ∑ answers : Q → A,
        ∏ q, (responses q).weight (answers q) *
          (if q = q₀ then h (answers q) else 1) := by
      apply Finset.sum_congr rfl
      intro answers _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ q, ∑ a, (responses q).weight a * (if q = q₀ then h a else 1) :=
      (Fintype.prod_sum (fun q a =>
        (responses q).weight a * (if q = q₀ then h a else 1))).symm
    _ = ∏ q : Q, if q = q₀ then (∑ a, (responses q₀).weight a * h a) else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = q₀
      · subst q
        simp
      · simp [hq, (responses q).normalized]
    _ = _ := by simp

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem expectation_comm (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → Γ → ℝ) :
    μ.expectation (fun x => ν.expectation (f x)) =
      ν.expectation (fun y => μ.expectation (fun x => f x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact mul_left_comm _ _ _

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]
end FiniteDistribution

end MaxCutGames.Foundations.Games

/-!
Exact finite sampling laws used to identify verifier distributions with repeated
game question laws. These are finite sum/product identities, not independence
assumptions about an unspecified distribution.
-/

namespace MaxCutGames.Foundations.Games.FiniteDistribution
open scoped BigOperators

theorem expectation_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (f : Ω → ℝ) :
    (uniform Ω).expectation f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  unfold expectation uniform
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv, mul_comm]

end MaxCutGames.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Basic2
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite prerequisites for Holenstein's consistent sampling argument (Lemma 5.2).

`firstAccepted` is an actual bounded rejection sampler on a shared finite list
of proposals. `first_union_common` proves its synchronization property.
The remaining theorems establish the exact overlap/union mass formulas and the
agreement lower bound used to analyze a first accepted shared proposal.

No infinite random process or locally computable embedding is asserted here.
-/

namespace MaxCutGames.Foundations.CorrelatedSampling

/-!
Exact finite probability mass of a bounded rejection process.

Each trial independently draws from a finite mass function `w`. Its first
accepted proposal is represented by `some proposal`; exhaustion is `none`.
The recursive definition exposes the one-step probability transition. We prove
normalization, nonnegativity, the exact survival probability, and an exact
agreement-event formula with the finite-truncation error.
-/

/-! A finite exact replacement for uniform real thresholds. A list of real
thresholds subdivides [0,1]. Each resulting interval is an atom with weight its
length. Every inserted threshold has exactly its stated acceptance mass. -/

/-! An actual finite probability rectangle implementing all thresholds from a
fixed finite list. The seed distribution is shared; each local acceptance test
depends only on its own density. -/

variable {α : Type*} [Fintype α]

def rectangleDistribution [Nonempty α] (thresholds : List ℝ) :
    Games.FiniteDistribution (RectangleSeed thresholds α) where
  weight := rectangleWeight thresholds
  nonnegative := rectangleWeight_nonnegative thresholds
  normalized := rectangleWeight_normalized thresholds

theorem rectangle_label_mass [DecidableEq α] (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : ∀ x, density x ∈ thresholds) (h0 : ∀ x, 0 ≤ density x)
    (h1 : ∀ x, density x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds density seed && decide (seed.1 = a)) =
      density a / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : α, if x = a then density x / (Fintype.card α : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a
      · simpa [hx] using rectangle_row_mass thresholds density x (hm x) (h0 x) (h1 x)
      · simp [hx]
    _ = density a / (Fintype.card α : ℝ) := by simp

omit [Fintype α] in theorem rectangle_or (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => max (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

theorem rectangle_union_mass (thresholds : List ℝ) (p q : α → ℝ)
    (hpm : ∀ a, p a ∈ thresholds) (hqm : ∀ a, q a ∈ thresholds)
    (hp0 : ∀ a, 0 ≤ p a) (_hq0 : ∀ a, 0 ≤ q a)
    (hp1 : ∀ a, p a ≤ 1) (hq1 : ∀ a, q a ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      unionMass p q / (Fintype.card α : ℝ) := by
  rw [rectangle_or]
  exact rectangle_acceptance_mass thresholds _
    (fun a => max_mem_thresholds thresholds (hpm a) (hqm a))
    (fun a => (hp0 a).trans (le_max_left _ _)) (fun a => max_le (hp1 a) (hq1 a))

theorem rectangle_common_label_mass [DecidableEq α] (thresholds : List ℝ)
    (p q : α → ℝ) (a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (_hq1 : ∀ x, q x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => (rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) &&
        decide (seed.1 = a)) = min (p a) (q a) / (Fintype.card α : ℝ) := by
  have hand := congrFun (rectangle_and thresholds p q)
  simp_rw [hand]
  exact rectangle_label_mass thresholds _ a
    (fun x => min_mem_thresholds thresholds (hpm x) (hqm x))
    (fun x => le_min (hp0 x) (hq0 x)) (fun x => (min_le_left _ _).trans (hp1 x))

end MaxCutGames.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_LabelBound
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Per-label diagonal lower bounds for the actual finite shared sampler.
These bounds retain the output label, which is necessary for comparing the
sampler's output distribution with a prescribed diagonal distribution. -/

namespace MaxCutGames.Foundations.CorrelatedSampling

section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

def localDiagonal (left right : σ → Bool) (decode : σ → α) (fallback a : α)
    (proposals : List σ) : ℝ :=
  if localSample left decode fallback proposals = a ∧
      localSample right decode fallback proposals = a then 1 else 0

omit [Fintype σ] [DecidableEq σ] in
theorem common_first_label_lower (left right : σ → Bool) (decode : σ → α)
    (fallback a : α) (proposals : List σ) :
    goodFirstIndicator (fun s => left s || right s) (goodLabel left right decode a) proposals ≤
      localDiagonal left right decode fallback a proposals := by
  cases hfirst : firstAccepted (fun s => left s || right s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      unfold localDiagonal
      split_ifs <;> norm_num
  | some s =>
      by_cases hc : goodLabel left right decode a s = true
      · have hparts : (left s = true ∧ right s = true) ∧ decode s = a := by
          simpa [goodLabel] using hc
        have h := first_union_common left right proposals s hfirst hparts.1.1 hparts.1.2
        simp [goodFirstIndicator, hfirst, hc, localDiagonal, localSample, h.1, h.2, hparts.2]
      · have hn : 0 ≤ localDiagonal left right decode fallback a proposals := by
          unfold localDiagonal
          split_ifs <;> norm_num
        simpa [goodFirstIndicator, hfirst, hc] using hn

omit [DecidableEq σ] in theorem union_goodLabel_mass
    (w : σ → ℝ) (left right : σ → Bool) (decode : σ → α) (a : α) :
    eventMass w (fun s => (left s || right s) && goodLabel left right decode a s) =
      eventMass w (goodLabel left right decode a) := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  cases hl : left s <;> cases hr : right s <;> simp [goodLabel, hl, hr]

/-- The finite shared-list sampler's mass on the particular diagonal output
(a,a) is at least the common-first-label mass. Exhaustion uses a fixed local
fallback; its contribution is nonnegative and is not counted in this bound. -/
theorem finite_label_diagonal_bound (w : σ → ℝ) (left right : σ → Bool)
    (decode : σ → α) (fallback a : α) (hw : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) (hu : 0 < eventMass w (fun s => left s || right s)) (n : Nat) :
    eventMass w (goodLabel left right decode a) / eventMass w (fun s => left s || right s) *
        (1 - eventMass w (fun s => !(left s || right s)) ^ n) ≤
      traceAverage w n (localDiagonal left right decode fallback a) := by
  have h := traceAverage_mono w hw n _ _ (common_first_label_lower left right decode fallback a)
  rw [goodFirstIndicator_law w _ _ hw_sum n,
    goodFirstMass_exact w _ _ hw_sum (ne_of_gt hu) n,
    union_goodLabel_mass] at h
  exact h

variable [Fintype α] [Nonempty α]

/-- Concrete normalized-density instance of the per-label bound. All random
proposals come from the finite rectangle constructed from `thresholds`. -/
theorem rectangle_label_diagonal_bound (thresholds : List ℝ) (p q : α → ℝ)
    (fallback a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (hq1 : ∀ x, q x ≤ 1)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (n : Nat) :
    min (p a) (q a) / (1 + totalVariation p q) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds p s || rectangleAccept thresholds q s)) ^ n) ≤
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds p) (rectangleAccept thresholds q)
          Prod.fst fallback a) := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hU : 0 < unionMass p q := by
    rw [unionMass_eq p q hpsum hqsum]
    linarith [totalVariation_nonneg p q]
  have hmass := rectangle_union_mass thresholds p q hpm hqm hp0 hq0 hp1 hq1
  have hu : 0 < eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds p s || rectangleAccept thresholds q s) := by
    rw [hmass]
    exact div_pos hU hc
  have h := finite_label_diagonal_bound (rectangleWeight thresholds)
    (rectangleAccept thresholds p) (rectangleAccept thresholds q) Prod.fst fallback a
    (rectangleWeight_nonnegative thresholds) (rectangleWeight_normalized thresholds) hu n
  unfold goodLabel at h
  rw [rectangle_common_label_mass thresholds p q a hpm hqm hp0 hq0 hp1 hq1, hmass] at h
  have hratio : (min (p a) (q a) / (Fintype.card α : ℝ)) /
      (unionMass p q / (Fintype.card α : ℝ)) = min (p a) (q a) / unionMass p q := by
    field_simp
  rw [hratio, unionMass_eq p q hpsum hqsum] at h
  exact h

end

/-!
A single finite rectangle proposal law for two finite families of distributions.
The subdivision includes every density appearing in either family.  Consequently
the local samplers share a seed space independently of their particular inputs.
-/

open scoped BigOperators

theorem distribution_weight_le_one {S : Type*} [Fintype S]
    (μ : Games.FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

def sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) : List ℝ :=
  profileThresholds (fun (k : Q₁ ⊕ Q₂) s => (Sum.elim L R k).weight s)

theorem left_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (s : S) :
    (L x).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inl x) s

theorem right_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) (s : S) :
    (R y).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inr y) s

abbrev SharedProfileSeed (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) :=
  RectangleSeed (sharedProfileThresholds L R) S

def sharedProfileLeft (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (L x).weight

def sharedProfileRight (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) : SharedProfileSeed L R → Bool :=
  rectangleAccept (sharedProfileThresholds L R) (R y).weight

def sharedProfileReject (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (y : Q₂) : ℝ :=
  eventMass (rectangleWeight (sharedProfileThresholds L R))
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s))

theorem sharedProfileReject_nonnegative [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : 0 ≤ sharedProfileReject L R x y := by
  exact eventMass_nonneg _ _
    (rectangleDistribution (α := S) (sharedProfileThresholds L R)).nonnegative

theorem sharedProfile_reject_le_rate [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : sharedProfileReject L R x y ≤ uniformRejectionRate S := by
  let thresholds := sharedProfileThresholds L R
  have hsum : (∑ s : RectangleSeed thresholds S, rectangleWeight thresholds s) = 1 :=
    (rectangleDistribution (α := S) thresholds).normalized
  have hcomp := eventMass_complement (rectangleWeight thresholds)
    (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) hsum
  have hu : eventMass (rectangleWeight thresholds)
      (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) =
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) := by
    change eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds (L x).weight s ||
        rectangleAccept thresholds (R y).weight s) = _
    rw [rectangle_union_mass thresholds (L x).weight (R y).weight
      (left_mem_sharedProfileThresholds L R x)
      (right_mem_sharedProfileThresholds L R y)
      (L x).nonnegative (R y).nonnegative
      (distribution_weight_le_one (L x)) (distribution_weight_le_one (R y))]
    rw [unionMass_eq (L x).weight (R y).weight (L x).normalized (R y).normalized]
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have htv := totalVariation_nonneg (L x).weight (R y).weight
  have hquot : 1 / (Fintype.card S : ℝ) ≤
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) :=
    (div_le_div_iff_of_pos_right hc).2 (by linarith)
  rw [hu] at hcomp
  change eventMass (rectangleWeight thresholds)
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s)) ≤
      1 - 1 / (Fintype.card S : ℝ)
  linarith

end MaxCutGames.Foundations.CorrelatedSampling

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

/-! Exact finite total variation and its event-probability bound. -/

namespace MaxCutGames.Foundations.Games.FiniteDistribution

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

def totalVariation (μ ν : FiniteDistribution Ω) : ℝ :=
  (∑ x, |μ.weight x - ν.weight x|) / 2

/-- A one-sided event difference is bounded by half the total absolute mass
difference. Normalization is used; the full absolute-mass sum would lose a
factor of two needed in the repetition argument. -/
theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end MaxCutGames.Foundations.Games.FiniteDistribution

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace MaxCutGames.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_inter_eq_mul_conditional (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given) :
    μ.probability (fun x => given x && event x) =
      μ.probability given * (μ.condition given positive).probability event := by
  have h := (eq_div_iff (ne_of_gt positive)).mp
    (μ.probability_condition given event positive)
  simpa only [mul_comm] using h.symm

end FiniteDistribution

end MaxCutGames.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Reindexing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coordinate reindexing for actual finite distributions and repeated games.
The joint questions are iid across coordinates; coordinate-success events
need not be independent. Strategies permute each player's local questions
and answers, so the resulting strategies remain local.
-/

noncomputable section

namespace MaxCutGames.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

theorem pushforward_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (e : Ω ≃ Γ) :
    μ.pushforward e = μ.transport e := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward, transport]
  have he : ∀ x : Ω, (e x = y) = (x = e.symm y) := by
    intro x
    apply propext
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  simp_rw [he]
  simp

end FiniteDistribution

end MaxCutGames.Foundations.Games
end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_UpperBound
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace MaxCutGames.Foundations.Games

open scoped BigOperators
noncomputable section

namespace FiniteDistribution

theorem pushforward_eq_of_agree_on_support
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f g : Ω → Γ)
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.pushforward f = μ.pushforward g := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]

/-- Applying separate maps to independent samples preserves their independence. -/
theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

end FiniteDistribution

end
end MaxCutGames.Foundations.Games

/-! Finite shared randomness is an actual convex mixture of distributions. -/

namespace MaxCutGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]

def mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) : FiniteDistribution Ω where
  weight x := ∑ seed, seedLaw.weight seed * (laws seed).weight x
  nonnegative x := Finset.sum_nonneg fun seed _ =>
    mul_nonneg (seedLaw.nonnegative seed) ((laws seed).nonnegative x)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (laws _).normalized, mul_one]
    exact seedLaw.normalized

theorem probability_mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) :
    (seedLaw.mixture laws).probability event =
      ∑ seed, seedLaw.weight seed * (laws seed).probability event := by
  unfold probability mixture
  calc
    _ = ∑ x, ∑ seed,
        seedLaw.weight seed * (if event x then (laws seed).weight x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      cases event x <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [Finset.mul_sum]

theorem probability_mixture_le (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) (bound : ℝ)
    (h : ∀ seed, (laws seed).probability event ≤ bound) :
    (seedLaw.mixture laws).probability event ≤ bound := by
  rw [probability_mixture]
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * bound :=
      Finset.sum_le_sum fun seed _ =>
        mul_le_mul_of_nonneg_left (h seed) (seedLaw.nonnegative seed)
    _ = bound := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

end
end MaxCutGames.Foundations.Games.FiniteDistribution

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_DistributionMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact composition identities for finite distribution maps. -/
namespace MaxCutGames.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end
end MaxCutGames.Foundations.Games.FiniteDistribution

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Overlap
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Direct diagonal-overlap comparison for the finite correlated sampler.
All quantities are finite weight arrays; no reference sampler or embedding
claim is assumed. The final theorem consumes the per-label lower bound that
is proved for the actual finite threshold sampler in CorrelatedSampling.
-/

namespace MaxCutGames.Foundations.Repetition

/-! Actual finite shared seed laws for the bounded correlated sampler. -/

open scoped BigOperators
open Games

universe u

def traceSeedLaw {σ : Type*} [Fintype σ] (μ : FiniteDistribution σ) :
    (n : Nat) → FiniteDistribution (TraceSeed σ n)
  | 0 => { weight := fun _ => 1, nonnegative := by intro; norm_num,
           normalized := by simp }
  | n + 1 => μ.product (traceSeedLaw μ n)

theorem traceSeedLaw_expectation {σ : Type*} [Fintype σ]
    (μ : FiniteDistribution σ) (n : Nat) (f : List σ → ℝ) :
    (traceSeedLaw μ n).expectation (fun seed => f (traceList n seed)) =
      CorrelatedSampling.traceAverage μ.weight n f := by
  induction n generalizing f with
  | zero => simp [traceSeedLaw, traceList, FiniteDistribution.expectation,
      CorrelatedSampling.traceAverage]
  | succ n ih =>
      change (μ.product (traceSeedLaw μ n)).expectation
        (fun seed => f (seed.1 :: traceList n seed.2)) = _
      rw [FiniteDistribution.expectation_product]
      simp only [CorrelatedSampling.traceAverage, FiniteDistribution.expectation]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact ih (fun xs => f (s :: xs))

open CorrelatedSampling

end MaxCutGames.Foundations.Repetition

/-!
Correlated rounding of finite partial assignments of equal density. A common
finite list of seeds is scanned locally at every vertex. An edge succeeds when
the first seed accepted by either endpoint is a jointly accepted good seed.
The finite truncation error is at most `(1 - density)^n`. Maximizing over the finite
set of deterministic labelings removes that error. No infinite random seed or
assumed rounding principle is used.
-/

namespace MaxCutGames.Repetition

section

open MaxCutGames.Foundations.Games
open MaxCutGames.Foundations.CorrelatedSampling
open MaxCutGames.Foundations.Repetition
open scoped BigOperators

variable {V S A : Type*} [Fintype V] [Fintype S] [Fintype A]

def partialPairMass (μ : FiniteDistribution S) (accept : V → S → Bool)
    (label : V → S → A) (R : V → V → A → A → Bool) (x y : V) : ℝ :=
  μ.probability (fun s => accept x s && accept y s && R x y (label x s) (label y s))

def partialEdgeMass {E : Type*} (μ : FiniteDistribution S) (accept : V → S → Bool)
    (label : V → S → A) (left right : E → V) (R : E → A → A → Bool) (e : E) : ℝ :=
  μ.probability (fun s => accept (left e) s && accept (right e) s &&
    R e (label (left e) s) (label (right e) s))

def partialLabelScore {E : Type*} [Fintype E] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool) (f : V → A) : ℝ :=
  ν.probability (fun e => R e (f (left e)) (f (right e)))

theorem expectation_mono_inline_RoundingSampling' {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

theorem expectation_const_inline_RoundingSampling' {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (c : ℝ) : μ.expectation (fun _ => c) = c := by
  simp [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized]

theorem expectation_partial_lower_inline_RoundingSampling {E : Type*} [Fintype E]
    (ν : FiniteDistribution E) (g : E → ℝ) (density tail : ℝ) :
    ν.expectation (fun xy => 2 * (g xy / density) - 1 - tail) =
      2 * (ν.expectation g / density) - 1 - tail := by
  unfold FiniteDistribution.expectation
  calc
    _ = ∑ xy, (2 / density * (ν.weight xy * g xy) - (1 + tail) * ν.weight xy) := by
      apply Finset.sum_congr rfl
      intro xy _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ν.normalized]
      ring

end

/-!
Exact finite threshold expansion for unit vectors.  A shared seed chooses one
coordinate and one atom of the common threshold partition.  Squared amplitudes
are acceptance probabilities, and joint acceptance has the coordinatewise
minimum law.  The construction permits arbitrary vertex-dependent labels and
arbitrary relations between their labels.
-/

open scoped BigOperators
open Foundations Games CorrelatedSampling

variable {V Ω A : Type*} [Fintype V] [Fintype Ω]

def thresholdDistribution [Nonempty Ω] (f : V → Ω → ℝ) :
    FiniteDistribution (ThresholdSeed f) := rectangleDistribution (thresholdLevels f)

/-- Every vertex accepts with the same positive mass, independently of its
unit vector.  Nonnegativity of the amplitudes is unnecessary for this lemma. -/
theorem threshold_acceptance_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) :
    (thresholdDistribution f).probability (thresholdAccept f x) = thresholdRate Ω := by
  change eventMass (rectangleWeight (thresholdLevels f))
    (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)) = _
  rw [rectangle_acceptance_mass (thresholdLevels f) _
    (square_mem_thresholdLevels f x) (fun ω => sq_nonneg (f x ω))
    (square_le_one_of_row_norm f hnorm x), hnorm x]
  rfl

/-- Joint acceptance with any relation on the two local labels has exactly the
minimum-overlap mass.  Both vertices use the same coordinate and threshold. -/
theorem threshold_good_pair_mass [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (a : V → Ω → A)
    (x y : V) (R : A → A → Prop) [DecidableRel R] :
    (thresholdDistribution f).probability (fun seed =>
      (thresholdAccept f x seed && thresholdAccept f y seed) &&
        decide (R (thresholdLabel f a x seed) (thresholdLabel f a y seed))) =
      thresholdRate Ω * ∑ ω,
        if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0 := by
  classical
  change (∑ seed : RectangleSeed (thresholdLevels f) Ω,
    if (rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2) seed &&
        rectangleAccept (thresholdLevels f) (fun ω => f y ω ^ 2) seed) &&
        decide (R (a x seed.1) (a y seed.1)) then
      rectangleWeight (thresholdLevels f) seed else 0) = _
  have hand := congrFun (rectangle_and (thresholdLevels f)
    (fun ω => f x ω ^ 2) (fun ω => f y ω ^ 2))
  simp_rw [hand]
  rw [Fintype.sum_prod_type]
  have hrow (ω : Ω) :
      (∑ i : Fin (thresholdPartition (thresholdLevels f)).length,
        if rectangleAccept (thresholdLevels f)
            (fun t => min (f x t ^ 2) (f y t ^ 2)) (ω, i) &&
            decide (R (a x ω) (a y ω)) then
          rectangleWeight (thresholdLevels f) (ω, i) else 0) =
        (if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0) /
          (Fintype.card Ω : ℝ) := by
    by_cases hR : R (a x ω) (a y ω)
    · simpa only [hR, decide_true, Bool.and_true, ite_true, if_true] using
        rectangle_row_mass (thresholdLevels f)
          (fun t => min (f x t ^ 2) (f y t ^ 2)) ω
          (min_mem_thresholds _ (square_mem_thresholdLevels f x ω)
            (square_mem_thresholdLevels f y ω))
          (le_min (sq_nonneg _) (sq_nonneg _))
          ((min_le_left _ _).trans (square_le_one_of_row_norm f hnorm x ω))
    · simp [hR]
  simp_rw [hrow]
  simp only [thresholdRate, div_eq_mul_inv, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact mul_comm _ _

/-- Boolean-predicate form used by finite games and the shared sampler. -/
theorem threshold_good_pair_mass_bool [Nonempty Ω] (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (a : V → Ω → A)
    (x y : V) (R : A → A → Bool) :
    (thresholdDistribution f).probability (fun seed =>
      (thresholdAccept f x seed && thresholdAccept f y seed) &&
        R (thresholdLabel f a x seed) (thresholdLabel f a y seed)) =
      thresholdRate Ω * ∑ ω,
        if R (a x ω) (a y ω) then min (f x ω ^ 2) (f y ω ^ 2) else 0 := by
  simpa only [Bool.decide_eq_true] using
    threshold_good_pair_mass f hnorm a x y (fun b c => R b c = true)

end MaxCutGames.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_AnalyticCheeger
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite threshold-overlap estimates used in the Dinur--Steurer argument.
These statements are numerical inequalities, not parallel-repetition premises.
The Boolean gate keeps the constraint predicate inside the overlap energy.
Weights need not be normalized: a finite auxiliary measure is permitted.
-/

/-! Finite vertex-specific padding of nonnegative vectors to unit squared row
mass. The new coordinates can only increase any nonnegative relation energy. -/

namespace MaxCutGames.Repetition

section

open scoped BigOperators
open Foundations.Games

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

theorem paddedAmplitude_row [DecidableEq V] (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v ≤ 1) (v : V) :
    rowSquareMass (paddedAmplitude f) v = 1 := by
  have hs : Real.sqrt (1 - rowSquareMass f v) ^ 2 = 1 - rowSquareMass f v :=
    Real.sq_sqrt (sub_nonneg.mpr (hrow v))
  simp only [rowSquareMass] at hs
  simp only [rowSquareMass, Fintype.sum_sum_type, paddedAmplitude]
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ v), hs]
  ring

def pairEnergy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then f (left e) ω * f (right e) ω else 0

def pairOverlap (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then min ((f (left e) ω) ^ 2) ((f (right e) ω) ^ 2) else 0

theorem pairEnergy_le_padded [DecidableEq V] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (fallback : A) :
    pairEnergy ν left right R a f ≤
      pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f) := by
  unfold pairEnergy FiniteDistribution.expectation
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (ν.nonnegative e)
  dsimp only
  rw [Fintype.sum_sum_type]
  simp only [paddedLabel, paddedAmplitude]
  have hnonneg : 0 ≤ ∑ w : V,
      if R e fallback fallback then
        (if left e = w then Real.sqrt (1 - rowSquareMass f (left e)) else 0) *
          (if right e = w then Real.sqrt (1 - rowSquareMass f (right e)) else 0)
      else 0 := by
    apply Finset.sum_nonneg
    intro w _
    split
    · exact mul_nonneg (paddedAmplitude_nonnegative f hf (left e) (Sum.inr w))
        (paddedAmplitude_nonnegative f hf (right e) (Sum.inr w))
    · exact le_rfl
  exact le_add_of_nonneg_right hnonneg

end

/-! Flatten the genuine finite occurrence law together with the auxiliary
coordinate into the Cheeger inequality. The occurrence may retain hidden
information; both endpoint label tables still depend only on their vertex. -/

open scoped BigOperators
open Foundations.Games

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

omit [Fintype V] in
theorem pairQuadraticMass_eq_one (ν : FiniteDistribution E) (left right : E → V)
    (f : V → Ω → ℝ) (hrow : ∀ v, rowSquareMass f v = 1) :
    Analytic.quadraticMass (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2) = 1 := by
  unfold Analytic.quadraticMass
  rw [Fintype.sum_prod_type]
  have he (e : E) :
      (∑ ω, ν.weight e * ((f (left e) ω) ^ 2 + (f (right e) ω) ^ 2) / 2) =
        ν.weight e := by
    calc
      _ = ν.weight e *
          ((∑ ω, (f (left e) ω) ^ 2) + (∑ ω, (f (right e) ω) ^ 2)) / 2 := by
        simp only [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.sum_mul]
      _ = ν.weight e := by
        change ν.weight e * (rowSquareMass f (left e) + rowSquareMass f (right e)) / 2 = _
        rw [hrow, hrow]
        ring
  simp_rw [he]
  exact ν.normalized

omit [Fintype V] in
theorem pairGatedCorrelation_eq_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedCorrelation (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairEnergy ν left right R a f := by
  simp only [Analytic.gatedCorrelation, pairEnergy, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

omit [Fintype V] in
theorem pairGatedMinimum_eq_overlap (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedMinimum (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairOverlap ν left right R a f := by
  simp only [Analytic.gatedMinimum, pairOverlap, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

omit [Fintype V] in
theorem pairEnergy_le_one_of_unit_rows (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v = 1) : pairEnergy ν left right R a f ≤ 1 := by
  have h := Analytic.gatedCorrelation_le_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1)
  rw [pairGatedCorrelation_eq_energy, pairQuadraticMass_eq_one ν left right f hrow] at h
  exact h

omit [Fintype V] in
/-- The overlap used by finite threshold sampling is large whenever the
actual weighted occurrence energy is large. -/
theorem pairOverlap_ge_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    1 - Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      pairOverlap ν left right R a f := by
  have h := Analytic.gatedMinimum_unit_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1) (fun p => hf (left p.1) p.2)
    (fun p => hf (right p.1) p.2) (pairQuadraticMass_eq_one ν left right f hrow)
  rw [pairGatedCorrelation_eq_energy, pairGatedMinimum_eq_overlap] at h
  exact h

end MaxCutGames.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Rounding
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! High-value rounding of finite nonnegative vectors. The finite threshold
partition and bounded shared rejection sampler produce an ordinary deterministic
labeling. The auxiliary edge sample may retain hidden constraint information;
the labeling receives only its local vertex. -/

namespace MaxCutGames.Repetition

section

open scoped BigOperators
open Foundations.Games

variable {V E A Ω : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype Ω]
  [Nonempty V] [Nonempty A] [Nonempty Ω]

omit [Fintype A] [Nonempty V] [Nonempty A] in
theorem threshold_average_good_mass (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v = 1) :
    ν.expectation (partialEdgeMass (thresholdDistribution f)
      (thresholdAccept f) (thresholdLabel f a) left right R) =
      thresholdRate Ω * pairOverlap ν left right R a f := by
  unfold partialEdgeMass pairOverlap FiniteDistribution.expectation
  simp_rw [threshold_good_pair_mass_bool f hrow a]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

end

/-!
Determinization of a nonnegative vector with one label chosen per vertex.
Every vertex retains its total mass. The objective is an arbitrary nonnegative
weighted sum of squares of linear functionals, so coefficients may have either
sign. Sampling complete label tables gives the original vector as its mean;
finite variance and an attained maximum then supply a deterministic table.
-/

section

open scoped BigOperators
open MaxCutGames.Foundations.Games

variable {V A T : Type*} [Fintype V] [Fintype A] [Fintype T]

/-- A zero row is harmless and uses a fixed fallback label. -/
def rowLaw [Nonempty A] (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (v : V) : FiniteDistribution A := by
  classical
  exact if hz : rowMass h v = 0 then
    { weight := fun a => if a = Classical.choice (inferInstance : Nonempty A) then 1 else 0
      nonnegative := fun a => by split <;> norm_num
      normalized := by simp }
  else
    { weight := fun a => h v a / rowMass h v
      nonnegative := fun a => div_nonneg (hh v a) (rowMass_nonnegative h hh v)
      normalized := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        exact mul_inv_cancel₀ hz }

omit [Fintype V] in
theorem rowLaw_expectation_mul_mass [Nonempty A] (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (v : V) (f : A → ℝ) :
    (rowLaw h hh v).expectation (fun a => f a * rowMass h v) =
      ∑ a, f a * h v a := by
  classical
  by_cases hz : rowMass h v = 0
  · have he : ∀ a, h v a = 0 := entry_eq_zero_of_rowMass_eq_zero h hh v hz
    simp [FiniteDistribution.expectation, hz, he]
  · simp only [rowLaw, hz, ↓reduceDIte, FiniteDistribution.expectation]
    apply Finset.sum_congr rfl
    intro a _
    field_simp [hz]

/-- Finite Jensen for the square, proved by expanding nonnegative variance. -/
theorem square_expectation_le {Ω : Type*} [Fintype Ω]
    (law : FiniteDistribution Ω) (f : Ω → ℝ) :
    law.expectation f ^ 2 ≤ law.expectation (fun x => f x ^ 2) := by
  let m := law.expectation f
  have h : 0 ≤ law.expectation (fun x => (f x - m) ^ 2) := by
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (law.nonnegative x) (sq_nonneg _)
  have he : law.expectation (fun x => (f x - m) ^ 2) =
      law.expectation (fun x => f x ^ 2) - m ^ 2 := by
    unfold FiniteDistribution.expectation
    calc
      _ = ∑ x, ((law.weight x * f x ^ 2 - 2 * m * (law.weight x * f x)) +
          law.weight x * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, law.normalized]
        change (law.expectation (fun x => f x ^ 2) - 2 * m * m) + 1 * m ^ 2 = _
        simp only [FiniteDistribution.expectation]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

theorem exists_expectation_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (law : FiniteDistribution Ω) (f : Ω → ℝ) :
    ∃ x, law.expectation f ≤ f x := by
  classical
  let M := Finset.univ.sup' Finset.univ_nonempty f
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset Ω)) Finset.univ_nonempty f
  refine ⟨x, ?_⟩
  calc
    law.expectation f ≤ ∑ y, law.weight y * M := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' f (Finset.mem_univ y)) (law.nonnegative y)
    _ = M := by rw [← Finset.sum_mul, law.normalized, one_mul]
    _ = f x := hx

/-- One label per vertex preserves every row's mass and can only improve the
nonnegative weighted squared image under any fixed linear map. In particular,
the same theorem applies separately at each coordinate of a vector-valued
assignment; no product or independence property of those coordinates is used. -/
theorem exists_deterministic_preserving_mass [Nonempty A]
    (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (c : T → V → A → ℝ) :
    ∃ labels : V → A,
      (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
        ∑ t, w t * (∑ v, c t v (labels v) * rowMass h v) ^ 2 := by
  classical
  let law := FiniteDistribution.table (rowLaw h hh)
  let X (t : T) (labels : V → A) : ℝ :=
    ∑ v, c t v (labels v) * rowMass h v
  have hmean (t : T) : law.expectation (X t) = ∑ v, ∑ a, c t v a * h v a := by
    change (∑ labels : V → A, law.weight labels *
      ∑ v, c t v (labels v) * rowMass h v) = _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    change (FiniteDistribution.table (rowLaw h hh)).expectation
      (fun labels => c t v (labels v) * rowMass h v) = _
    exact (FiniteDistribution.expectation_table_eval (rowLaw h hh) v
      (fun a => c t v a * rowMass h v)).trans
        (rowLaw_expectation_mul_mass h hh v (c t v))
  have hjensen (t : T) : (∑ v, ∑ a, c t v a * h v a) ^ 2 ≤
      law.expectation (fun labels => X t labels ^ 2) := by
    rw [← hmean]
    exact square_expectation_le law (X t)
  have hsum : (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
      ∑ t, w t * law.expectation (fun labels => X t labels ^ 2) := by
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_mul_of_nonneg_left (hjensen t) (hw t)
  have heq : (∑ t, w t * law.expectation (fun labels => X t labels ^ 2)) =
      law.expectation (fun labels => ∑ t, w t * X t labels ^ 2) := by
    unfold FiniteDistribution.expectation
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro labels _
    apply Finset.sum_congr rfl
    intro t _
    ring
  obtain ⟨labels, hlabels⟩ := exists_expectation_le law
    (fun labels => ∑ t, w t * X t labels ^ 2)
  rw [heq] at hsum
  exact ⟨labels, hsum.trans hlabels⟩

/-- The same conclusion stated directly as a deterministic nonnegative vector.
Its row masses are exactly those of the original vector. -/
theorem exists_deterministic_vector [Nonempty A] [DecidableEq A]
    (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (c : T → V → A → ℝ) :
    ∃ labels : V → A,
      (∀ v a, 0 ≤ deterministicVector h labels v a) ∧
      (∀ v, rowMass (deterministicVector h labels) v = rowMass h v) ∧
      (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
        ∑ t, w t * (∑ v, ∑ a, c t v a * deterministicVector h labels v a) ^ 2 := by
  obtain ⟨labels, hlabels⟩ := exists_deterministic_preserving_mass h hh w hw c
  refine ⟨labels, deterministicVector_nonnegative h hh labels,
    deterministicVector_rowMass h labels, ?_⟩
  simpa only [deterministicVector_linear_image] using hlabels

end

/-!
Finite conditional projection kernels for the Dinur--Steurer argument.
The outer distribution samples the right question and the inner distribution
samples the left question conditional on it. These are genuine normalized
finite distributions; no norm inequality or repetition claim is a field.
-/

open MaxCutGames.Foundations.Games
open scoped BigOperators

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

/-- Squared Hilbert norm, with the actual right-question marginal. -/
def energy (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Q₁ → A₁ → ℝ) : ℝ :=
  ∑ y, K.outer.weight y * ∑ b, K.apply f y b ^ 2

def assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) : ℝ := K.energy (assignment labels)

/-- Maximum squared collision norm of an ordinary deterministic left strategy. -/
def collisionValue [Nonempty A₁] (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty K.assignmentEnergy

def vectorEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) : ℝ := ∑ ω, K.energy (f ω)

theorem energy_nonneg (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) : 0 ≤ K.energy f := by
  exact Finset.sum_nonneg fun y _ => mul_nonneg (K.outer.nonnegative y)
    (Finset.sum_nonneg fun b _ => sq_nonneg _)

theorem assignmentEnergy_le_collisionValue [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    K.assignmentEnergy labels ≤ K.collisionValue := by
  classical
  exact Finset.le_sup' _ (Finset.mem_univ labels)

theorem collisionValue_le_iff [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    K.collisionValue ≤ bound ↔ ∀ labels, K.assignmentEnergy labels ≤ bound := by
  classical
  simp [collisionValue, Finset.sup'_le_iff]

theorem exists_optimal_assignment [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    ∃ labels, K.assignmentEnergy labels = K.collisionValue := by
  classical
  obtain ⟨labels, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Q₁ → A₁))) Finset.univ_nonempty K.assignmentEnergy
  exact ⟨labels, h.symm⟩

theorem collisionValue_nonneg [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : 0 ≤ K.collisionValue := by
  obtain ⟨labels, h⟩ := K.exists_optimal_assignment
  rw [← h]
  exact K.energy_nonneg _

end ProjectionKernel
end MaxCutGames.Repetition

/-!
The collision norm as an actual finite distribution on symmetrized edges.
An edge retains the hidden common right question, while each label remains a
function of its own left question.  Projection uniqueness turns the sum over
common right answers into a Boolean compatibility predicate exactly.
-/

namespace MaxCutGames.Repetition.ProjectionKernel

section

open Foundations.Games
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def symmetricDistribution (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    FiniteDistribution (SymmetricEdge Q₁ Q₂) where
  weight e := K.outer.weight e.1 * (K.inner e.1).weight e.2.1 *
    (K.inner e.1).weight e.2.2
  nonnegative e := mul_nonneg
    (mul_nonneg (K.outer.nonnegative _) ((K.inner _).nonnegative _))
    ((K.inner _).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ y, K.outer.weight y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Fintype.sum_prod_type]
        calc
          _ = ∑ x, K.outer.weight y * (K.inner y).weight x := by
            apply Finset.sum_congr rfl
            intro x _
            dsimp only
            rw [← Finset.mul_sum, (K.inner y).normalized, mul_one]
          _ = K.outer.weight y := by
            rw [← Finset.mul_sum, (K.inner y).normalized, mul_one]
      _ = 1 := K.outer.normalized

def symmetricAccept (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (e : SymmetricEdge Q₁ Q₂) (a a' : A₁) : Bool := by
  classical
  exact decide (∃ b, K.accepts e.2.1 e.1 a b = true ∧
    K.accepts e.2.2 e.1 a' b = true)

theorem sum_projection_gates (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (y : Q₂) (x x' : Q₁) (a a' : A₁) (r s : ℝ) :
    (∑ b, (if K.accepts x y a b then r else 0) *
      (if K.accepts x' y a' b then s else 0)) =
        if K.symmetricAccept (y, x, x') a a' then r * s else 0 := by
  classical
  by_cases hex : ∃ b, K.accepts x y a b = true ∧ K.accepts x' y a' b = true
  · obtain ⟨b₀, hb₀, hb₀'⟩ := hex
    have hex' : ∃ b, K.accepts x y a b = true ∧ K.accepts x' y a' b = true :=
      ⟨b₀, hb₀, hb₀'⟩
    simp only [symmetricAccept, hex', decide_true, ite_true, if_true]
    calc
      _ = (if K.accepts x y a b₀ then r else 0) *
          (if K.accepts x' y a' b₀ then s else 0) := by
        apply Finset.sum_eq_single b₀
        · intro b _ hne
          have hb : K.accepts x y a b ≠ true := by
            intro hb
            exact hne (K.projection x y a b b₀ hb hb₀)
          simp [hb]
        · simp
      _ = r * s := by simp [hb₀, hb₀']
  · simp only [symmetricAccept, hex, decide_false, Bool.false_eq_true, ite_false]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : K.accepts x y a b = true
    · have hb' : K.accepts x' y a' b ≠ true := fun hb' => hex ⟨b, hb, hb'⟩
      simp [hb']
    · simp [hb]

theorem apply_single_label (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (f : Q₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => if labels x = a then f x else 0) y b =
      ∑ x, (K.inner y).weight x * (if K.accepts x y (labels x) b then f x else 0) := by
  classical
  unfold apply
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  calc
    _ = ∑ a, if labels x = a then
        (if K.accepts x y (labels x) b then f x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : labels x = a
      · subst a
        simp
      · simp [ha]
    _ = _ := by simp

theorem energy_single_label (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (f : Q₁ → ℝ) :
    K.energy (fun x a => if labels x = a then f x else 0) =
      K.symmetricDistribution.expectation (fun e =>
        if K.symmetricAccept e (labels (symmetricLeft e)) (labels (symmetricRight e))
          then f (symmetricLeft e) * f (symmetricRight e) else 0) := by
  classical
  have hexpand (y : Q₂) :
      (∑ b, (∑ x, (K.inner y).weight x *
        (if K.accepts x y (labels x) b then f x else 0)) ^ 2) =
      ∑ x, ∑ x', (K.inner y).weight x * (K.inner y).weight x' *
        (if K.symmetricAccept (y, x, x') (labels x) (labels x')
          then f x * f x' else 0) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' _
    calc
      _ = (K.inner y).weight x * (K.inner y).weight x' *
          ∑ b, (if K.accepts x y (labels x) b then f x else 0) *
            (if K.accepts x' y (labels x') b then f x' else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [K.sum_projection_gates]
  unfold energy
  simp_rw [K.apply_single_label, hexpand]
  simp only [FiniteDistribution.expectation, symmetricDistribution,
    Fintype.sum_prod_type, symmetricLeft, symmetricRight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  simp only [mul_assoc]
  rfl

/-- Coordinate expansion and the symmetrized edge law agree exactly. -/
theorem vectorEnergy_singleLabelVector (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (a : Q₁ → Ω → A₁) (f : Q₁ → Ω → ℝ) :
    K.vectorEnergy (singleLabelVector a f) =
      pairEnergy K.symmetricDistribution symmetricLeft symmetricRight K.symmetricAccept a f := by
  classical
  unfold vectorEnergy singleLabelVector
  simp_rw [K.energy_single_label]
  unfold pairEnergy FiniteDistribution.expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]

/-- Ordinary deterministic labelings give the collision assignment energy. -/
theorem symmetric_probability_eq_assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) :
    K.symmetricDistribution.probability (fun e =>
      K.symmetricAccept e (labels (symmetricLeft e)) (labels (symmetricRight e))) =
        K.assignmentEnergy labels := by
  classical
  change _ = K.energy (fun x a => if labels x = a then (1 : ℝ) else 0)
  rw [K.energy_single_label]
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    mul_ite, mul_one, mul_zero]

end

/-!
Apply finite positive-vector determinization to the actual projection kernel.
The target coordinates retain both the right question and the right answer.
The selected label may depend on the auxiliary coordinate, but only on its own
left question. Every question's squared vector mass is preserved exactly.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

/-- Explicit matrix coefficients of the projection operator. -/
def linearCoefficient (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (t : Q₂ × A₂) (x : Q₁) (a : A₁) : ℝ :=
  (K.inner t.1).weight x * (if K.accepts x t.1 a t.2 then 1 else 0)

theorem apply_eq_linearCoefficient_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply h y b = ∑ x, ∑ a, K.linearCoefficient (y, b) x a * h x a := by
  unfold apply
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : K.accepts x y a b = true <;> simp [linearCoefficient, ha]

theorem energy_eq_linearCoefficient_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) :
    K.energy h = ∑ t : Q₂ × A₂, K.outer.weight t.1 *
      (∑ x, ∑ a, K.linearCoefficient t x a * h x a) ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← K.apply_eq_linearCoefficient_sum, ← Finset.mul_sum]
  rfl

/-- Scalar kernel determinization preserves the whole mass at every question. -/
theorem exists_energy_le_deterministicVector [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) (hh : ∀ x a, 0 ≤ h x a) :
    ∃ labels : Q₁ → A₁,
      K.energy h ≤ K.energy (deterministicVector h labels) := by
  classical
  obtain ⟨labels, _, _, hlabels⟩ := exists_deterministic_vector h hh
    (fun t : Q₂ × A₂ => K.outer.weight t.1)
    (fun t => K.outer.nonnegative t.1) K.linearCoefficient
  refine ⟨labels, ?_⟩
  rw [K.energy_eq_linearCoefficient_sum, K.energy_eq_linearCoefficient_sum]
  exact hlabels

/-- Auxiliary coordinates are determinized separately; they need not be
independent, normalized, or nonempty. -/
theorem exists_vectorEnergy_le_singleLabelVector [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Ω → Q₁ → A₁ → ℝ) (hh : ∀ ω x a, 0 ≤ h ω x a) :
    ∃ labels : Q₁ → Ω → A₁,
      K.vectorEnergy h ≤ K.vectorEnergy (singleLabelVector labels (vectorAmplitude h)) := by
  classical
  have hex (ω : Ω) := K.exists_energy_le_deterministicVector (h ω) (hh ω)
  let labels (ω : Ω) : Q₁ → A₁ := Classical.choose (hex ω)
  have hlabels (ω : Ω) : K.energy (h ω) ≤
      K.energy (deterministicVector (h ω) (labels ω)) := Classical.choose_spec (hex ω)
  refine ⟨fun x ω => labels ω x, ?_⟩
  apply Finset.sum_le_sum
  intro ω _
  have heq : deterministicVector (h ω) (labels ω) =
      singleLabelVector (fun x ω => labels ω x) (vectorAmplitude h) ω := by
    funext x a
    by_cases ha : a = labels ω x
    · simp [deterministicVector, singleLabelVector, vectorAmplitude, ha]
    · simp [deterministicVector, singleLabelVector, ha, Ne.symm ha]
  exact heq ▸ hlabels ω

end MaxCutGames.Repetition.ProjectionKernel

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ProductCollisionBounds
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Soundness.ConditionalIncidences.zeroBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Comparison of the actual classical game value with the squared collision
norm. Both directions are proved for the normalized conditional kernel, including
partial projection constraints and zero-weight questions. -/

namespace MaxCutGames.Repetition

noncomputable section

namespace ProjectionKernel

open MaxCutGames.Foundations.Games
open scoped BigOperators

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

theorem sq_expectation_le_expectation_sq {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → ℝ) :
    μ.expectation f ^ 2 ≤ μ.expectation (fun x => f x ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset Ω))
    (r := fun x => μ.weight x * f x)
    (f := μ.weight) (g := fun x => μ.weight x * f x ^ 2)
    (fun x _ => μ.nonnegative x)
    (fun x _ => mul_nonneg (μ.nonnegative x) (sq_nonneg _))
    (fun x _ => by ring_nf; exact le_rfl)
  simpa only [μ.normalized, one_mul, FiniteDistribution.expectation] using h

/-- The projected distribution has total mass at most one; missing mass is the
possibility that a partial projection rejects the chosen left answer. -/
theorem sum_apply_assignment_le_one (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) :
    (∑ b, K.apply (assignment labels) y b) ≤ 1 := by
  classical
  simp only [apply_assignment]
  rw [Finset.sum_comm, ← (K.inner y).normalized]
  apply Finset.sum_le_sum
  intro x _
  by_cases hex : ∃ b, K.accepts x y (labels x) b = true
  · obtain ⟨b₀, hb₀⟩ := hex
    have hiff : ∀ b, K.accepts x y (labels x) b = true ↔ b = b₀ := by
      intro b
      constructor
      · intro hb
        exact K.projection x y (labels x) b b₀ hb hb₀
      · rintro rfl
        exact hb₀
    simp only [hiff]
    simp
  · have hnone : ∀ b, K.accepts x y (labels x) b ≠ true := by
      intro b hb
      exact hex ⟨b, hb⟩
    simpa [hnone] using (K.inner y).nonnegative x

theorem success_eq_outer_apply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) :
    K.toGame.success s =
      K.outer.expectation (fun y => K.apply (assignment s.1) y (s.2 y)) := by
  classical
  simp only [Game.success, Game.wins, toGame, FiniteDistribution.probability,
    FiniteDistribution.expectation, apply_assignment, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : K.accepts x y (s.1 x) (s.2 y) = true <;> simp [h]

theorem success_sq_le_assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) :
    K.toGame.success s ^ 2 ≤ K.assignmentEnergy s.1 := by
  rw [success_eq_outer_apply]
  calc
    _ ≤ K.outer.expectation
        (fun y => K.apply (assignment s.1) y (s.2 y) ^ 2) :=
      sq_expectation_le_expectation_sq K.outer _
    _ ≤ K.assignmentEnergy s.1 := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (K.outer.nonnegative y)
      exact Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ (s.2 y))

/-- Choose the actual best right answer separately at each right question. -/
theorem exists_best_response [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    ∃ answers : Q₂ → A₂, ∀ y b,
      K.apply (assignment labels) y b ≤ K.apply (assignment labels) y (answers y) := by
  classical
  have h : ∀ y, ∃ b : A₂, ∀ b',
      K.apply (assignment labels) y b' ≤ K.apply (assignment labels) y b := by
    intro y
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset A₂)) Finset.univ_nonempty
      (fun b => K.apply (assignment labels) y b)
    refine ⟨b, fun b' => ?_⟩
    rw [← hb]
    exact Finset.le_sup' _ (Finset.mem_univ b')
  exact ⟨fun y => Classical.choose (h y), fun y b => Classical.choose_spec (h y) b⟩

/-! The alphabet-independent high-value bound for the actual projection
operator. Positive vectors are determinized, padded, and rounded using proved
finite constructions. No rounding or repetition hypothesis is exposed. -/

theorem distribution_nonempty_inline_RoundingKernel {T : Type*} [Fintype T]
    (μ : FiniteDistribution T) : Nonempty T := by
  by_contra h
  have : IsEmpty T := not_nonempty_iff.mp h
  have hz : (∑ t, μ.weight t) = 0 := by simp
  linarith [μ.normalized]

end ProjectionKernel

/-!
Finite-sum tensor factorization used by projection-game collision operators.
No restriction to coordinatewise strategies occurs: `f` below is an arbitrary
function of both input questions and both input answers.
-/

namespace ProjectionKernel

open MaxCutGames.Foundations.Games
open scoped BigOperators

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Ω I : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Ω] [Fintype I]

/-! Exact tensor identities for normalized finite projection kernels. -/

/-- The coefficient form of the conditional projection operator. -/
def coefficients (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (y : Q₂) (b : A₂) (x : Q₁) (a : A₁) : ℝ :=
  (K.inner y).weight x * if K.accepts x y a b then 1 else 0

theorem apply_eq_kernelApply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply f y b = kernelApply K.coefficients f y b := by
  classical
  unfold apply kernelApply coefficients
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : K.accepts x y a b = true <;> simp [h]

theorem apply_nonnegative (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (hf : ∀ x a, 0 ≤ f x a) (y : Q₂) (b : A₂) :
    0 ≤ K.apply f y b := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg ((K.inner y).nonnegative x)
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hf x a
  · exact le_rfl

theorem apply_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : I → Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => ∑ i, f i x a) y b = ∑ i, K.apply (f i) y b := by
  simp_rw [apply_eq_kernelApply]
  exact kernelApply_sum _ _ _ _

theorem apply_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => r * f x a) y b = r * K.apply f y b := by
  simp_rw [apply_eq_kernelApply]
  exact kernelApply_smul _ _ _ _ _

/-- Independent product of the outer and conditional laws. -/
def product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    ProjectionKernel (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) where
  outer := K.outer.product H.outer
  inner q := (K.inner q.1).product (H.inner q.2)
  accepts x y a b := K.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2
  projection x y a b b' hb hb' := by
    have h₁ := Bool.and_eq_true_iff.mp hb
    have h₂ := Bool.and_eq_true_iff.mp hb'
    exact Prod.ext (K.projection _ _ _ _ _ h₁.1 h₂.1)
      (H.projection _ _ _ _ _ h₁.2 h₂.2)

theorem coefficients_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    (K.product H).coefficients = tensorKernel K.coefficients H.coefficients := by
  funext yz bc xu ad
  unfold coefficients product tensorKernel FiniteDistribution.product
  by_cases hk : K.accepts xu.1 yz.1 ad.1 bc.1 = true <;>
    by_cases hh : H.accepts xu.2 yz.2 ad.2 bc.2 = true <;> simp [hk, hh]

/-- Arbitrary product inputs factor through the second game operator. -/
theorem apply_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (f : (Q₁ × R₁) → (A₁ × B₁) → ℝ)
    (y : Q₂) (z : R₂) (b : A₂) (c : B₂) :
    (K.product H).apply f (y,z) (b,c) =
      K.apply (fun x a => H.apply (fun u d => f (x,u) (a,d)) z c) y b := by
  simp_rw [apply_eq_kernelApply]
  rw [coefficients_product]
  exact kernelApply_tensor _ _ _ _ _ _ _

/-!
The tensor-domination reduction before the Dinur--Steurer rounding theorem.
Every deterministic strategy for the product gives a nonnegative vector table
for the first kernel. Its energy is exactly the product collision energy, and
each input-question mass is bounded by the second kernel's collision value.
-/

/-- Apply the second game to a fixed first question and first answer. The
square-root factor changes its weighted output space into counting measure. -/
def tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁))
    (ω : R₂ × B₂) (x : Q₁) (a : A₁) : ℝ :=
  Real.sqrt (H.outer.weight ω.1) *
    H.apply (fun u d => assignment labels (x,u) (a,d)) ω.1 ω.2

omit [Fintype Q₁] [Fintype A₁] in
theorem tensorSlice_nonnegative (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) (a : A₁) :
    0 ≤ H.tensorSlice labels ω x a := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply H.apply_nonnegative
  intro u d
  unfold assignment
  split
  · exact zero_le_one
  · exact le_rfl

omit [Fintype Q₁] [Fintype R₁] [Fintype B₁] in
/-- Marginalizing the first label of a deterministic product strategy leaves
the deterministic second-label strategy. -/
theorem sum_assignment_product (labels : (Q₁ × R₁) → (A₁ × B₁))
    (x : Q₁) (u : R₁) (d : B₁) :
    (∑ a, assignment labels (x,u) (a,d)) =
      assignment (fun r => (labels (x,r)).2) u d := by
  classical
  by_cases h : (labels (x,u)).2 = d <;> simp [assignment, Prod.ext_iff, h]

omit [Fintype Q₁] in
theorem tensorSlice_label_mass (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (ω : R₂ × B₂) (x : Q₁) :
    (∑ a, H.tensorSlice labels ω x a) =
      Real.sqrt (H.outer.weight ω.1) *
        H.apply (assignment (fun r => (labels (x,r)).2)) ω.1 ω.2 := by
  unfold tensorSlice
  rw [← Finset.mul_sum, ← apply_sum]
  simp_rw [sum_assignment_product]

omit [Fintype Q₁] in
/-- The fiber mass is an actual collision energy of the second game, not a
free normalization assumption. -/
theorem vectorMass_tensorSlice (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x =
      H.assignmentEnergy (fun r => (labels (x,r)).2) := by
  classical
  unfold vectorMass assignmentEnergy energy
  simp_rw [tensorSlice_label_mass, mul_pow]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Real.sq_sqrt (H.outer.nonnegative y), Finset.mul_sum]

omit [Fintype Q₁] in
theorem vectorMass_tensorSlice_le [Nonempty B₁]
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) (x : Q₁) :
    vectorMass (H.tensorSlice labels) x ≤ H.collisionValue := by
  rw [vectorMass_tensorSlice]
  exact H.assignmentEnergy_le_collisionValue _

/-- Exact Hilbert-norm factorization, with every marginal weight retained. -/
theorem vectorEnergy_tensorSlice (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (labels : (Q₁ × R₁) → (A₁ × B₁)) :
    K.vectorEnergy (H.tensorSlice labels) = (K.product H).assignmentEnergy labels := by
  classical
  let p := fun y z b c =>
    K.apply (fun x a => H.apply (fun u d => assignment labels (x,u) (a,d)) z c) y b ^ 2
  have hlhs : K.vectorEnergy (H.tensorSlice labels) =
      ∑ z, ∑ c, ∑ y, ∑ b, K.outer.weight y * H.outer.weight z * p y z b c := by
    simp only [vectorEnergy, energy, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change K.outer.weight y *
      (K.apply (fun x a => Real.sqrt (H.outer.weight z) *
        H.apply (fun u d => assignment labels (x,u) (a,d)) z c) y b) ^ 2 = _
    rw [apply_smul, mul_pow, Real.sq_sqrt (H.outer.nonnegative z)]
    exact (mul_assoc _ _ _).symm
  have hrhs : (K.product H).assignmentEnergy labels =
      ∑ y, ∑ z, ∑ b, ∑ c, K.outer.weight y * H.outer.weight z * p y z b c := by
    simp only [assignmentEnergy, energy, product, FiniteDistribution.product,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro z _
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    exact congrArg (fun r : ℝ => r ^ 2)
      (apply_product K H (assignment labels) y z b c)
  rw [hlhs, hrhs]
  calc
    (∑ z, ∑ c, ∑ y, ∑ b, K.outer.weight y * H.outer.weight z * p y z b c) =
        ∑ z, ∑ y, ∑ b, ∑ c, K.outer.weight y * H.outer.weight z * p y z b c := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-! Homogeneous normalization for finite nonnegative vector assignments. -/

theorem energy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) :
    K.energy (fun x a => r * f x a) = r ^ 2 * K.energy f := by
  unfold energy
  simp_rw [apply_smul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_left_comm _ _ _

theorem vectorEnergy_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) :
    K.vectorEnergy (fun ω x a => r * f ω x a) = r ^ 2 * K.vectorEnergy f := by
  unfold vectorEnergy
  simp_rw [energy_smul]
  exact (Finset.mul_sum _ _ _).symm

theorem vectorEnergy_eq_zero_of_mass_nonpositive
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) : K.vectorEnergy f = 0 := by
  have hfzero : f = fun _ _ _ => 0 := by
    funext ω x a
    exact entry_eq_zero_of_vectorMass_nonpositive f hf hmass ω x a
  rw [hfzero]
  simp [vectorEnergy, energy, apply]

/-- A unit-mass estimate extends to any nonnegative mass bound, including
zero. The hypothesis is precisely the unit-mass analytic estimate being
normalized; the normalization itself assumes no repetition bound. -/
theorem vectorEnergy_le_of_unit_bound
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (ρ C : ℝ)
    (unit_bound : ∀ f : Ω → Q₁ → A₁ → ℝ,
      (∀ ω x a, 0 ≤ f ω x a) → (∀ x, vectorMass f x ≤ 1) → K.vectorEnergy f ≤ ρ)
    (hC : 0 ≤ C) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ C) :
    K.vectorEnergy f ≤ ρ * C := by
  rcases eq_or_lt_of_le hC with hzero | hpositive
  · have hCzero : C = 0 := hzero.symm
    subst C
    rw [K.vectorEnergy_eq_zero_of_mass_nonpositive f hf hmass, mul_zero]
  · have hsqrt : 0 ≤ (Real.sqrt C)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg C)
    have hscale : ((Real.sqrt C)⁻¹) ^ 2 = C⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hC]
    have hnorm : ∀ x, vectorMass (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a) x ≤ 1 := by
      intro x
      rw [vectorMass_smul, hscale]
      have h := mul_le_mul_of_nonneg_left (hmass x) (inv_nonneg.mpr hC)
      simpa [ne_of_gt hpositive] using h
    have hbound := unit_bound (fun ω x a => (Real.sqrt C)⁻¹ * f ω x a)
      (fun ω x a => mul_nonneg hsqrt (hf ω x a)) hnorm
    rw [vectorEnergy_smul, hscale] at hbound
    have h := mul_le_mul_of_nonneg_left hbound hC
    simpa [← mul_assoc, ne_of_gt hpositive, mul_comm C ρ] using h

/-!
Collision norms are unchanged by bijective encodings of either player's
questions and answers. The distributions, acceptance predicate, and assignment
tables are transported together. This provides the finite-tuple regrouping
needed to pass from one product step to arbitrary parallel repetition.
-/

/-- Transport both normalized question laws and the projection predicate. -/
def reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) : ProjectionKernel R₁ R₂ B₁ B₂ where
  outer := K.outer.transport eQ₂
  inner y := (K.inner (eQ₂.symm y)).transport eQ₁
  accepts x y a b := K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
  projection := by
    intro x y a b b' hb hb'
    exact eA₂.symm.injective (K.projection _ _ _ _ _ hb hb')

/-- Reindexing the operator equals pulling back its assignment table. -/
theorem apply_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂)
    (f : R₁ → B₁ → ℝ) (y : R₂) (b : B₂) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).apply f y b =
      K.apply (fun x a => f (eQ₁ x) (eA₁ a)) (eQ₂.symm y) (eA₂.symm b) := by
  classical
  unfold apply
  change (∑ x, (K.inner (eQ₂.symm y)).weight (eQ₁.symm x) *
    ∑ a, if K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
      then f x a else 0) = _
  refine Fintype.sum_equiv eQ₁.symm _ _ ?_
  intro x
  simp only [Equiv.apply_symm_apply]
  congr 1
  refine Fintype.sum_equiv eA₁.symm _ _ ?_
  intro a
  simp only [Equiv.apply_symm_apply]

theorem energy_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) (f : R₁ → B₁ → ℝ) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).energy f =
      K.energy (fun x a => f (eQ₁ x) (eA₁ a)) := by
  classical
  unfold energy
  simp_rw [apply_reindex]
  change (∑ y, K.outer.weight (eQ₂.symm y) *
    ∑ b, K.apply (fun x a => f (eQ₁ x) (eA₁ a)) (eQ₂.symm y) (eA₂.symm b) ^ 2) = _
  refine Fintype.sum_equiv eQ₂.symm _ _ ?_
  intro y
  congr 1
  exact Fintype.sum_equiv eA₂.symm _ _ (fun _ => rfl)

theorem assignmentEnergy_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) (labels : R₁ → B₁) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).assignmentEnergy labels =
      K.assignmentEnergy (fun x => eA₁.symm (labels (eQ₁ x))) := by
  classical
  unfold assignmentEnergy
  rw [energy_reindex]
  congr 1
  funext x a
  unfold assignment
  have h : labels (eQ₁ x) = eA₁ a ↔ eA₁.symm (labels (eQ₁ x)) = a := by
    constructor
    · intro ha
      rw [ha, Equiv.symm_apply_apply]
    · intro ha
      calc
        labels (eQ₁ x) = eA₁ (eA₁.symm (labels (eQ₁ x))) :=
          (eA₁.apply_symm_apply _).symm
        _ = eA₁ a := congrArg eA₁ ha
  rw [h]

/-- No strategy is lost under bijective question and answer encodings. -/
theorem collisionValue_reindex [Nonempty A₁] [Nonempty B₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).collisionValue = K.collisionValue := by
  classical
  apply le_antisymm
  · apply ((K.reindex eQ₁ eQ₂ eA₁ eA₂).collisionValue_le_iff _).2
    intro labels
    rw [assignmentEnergy_reindex]
    exact K.assignmentEnergy_le_collisionValue _
  · apply (K.collisionValue_le_iff _).2
    intro labels
    have h := (K.reindex eQ₁ eQ₂ eA₁ eA₂).assignmentEnergy_le_collisionValue
      (fun x => eA₁ (labels (eQ₁.symm x)))
    simpa only [assignmentEnergy_reindex, Equiv.symm_apply_apply] using h

end ProjectionKernel

end

end MaxCutGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_KernelIteration
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Independent repetitions of the actual conditional projection kernel. The
resulting game has precisely the original game's product question law. A
successor tuple is a reindexed independent product, so collision bounds on the
product apply to unrestricted strategies on whole tuples.
-/

namespace MaxCutGames.Repetition.ProjectionKernel

open MaxCutGames.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

theorem eq_of_data_eq {K H : ProjectionKernel Q₁ Q₂ A₁ A₂}
    (houter : K.outer = H.outer) (hinner : K.inner = H.inner)
    (haccepts : K.accepts = H.accepts) : K = H := by
  cases K
  cases H
  cases houter
  cases hinner
  cases haccepts
  rfl

/-- Separate the first coordinate without restricting answer dependence on
any coordinate of the complete local question tuple. -/
theorem repetition_succ (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    K.repetition (n + 1) =
      (K.product (K.repetition n)).reindex
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => Q₂))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₁))
        (Fin.consEquiv (fun _ : Fin (n + 1) => A₂)) := by
  classical
  apply eq_of_data_eq
  · apply FiniteDistribution.eq_of_weight_eq
    intro y
    change (∏ i : Fin (n + 1), K.outer.weight (y i)) =
      K.outer.weight (y 0) * ∏ i : Fin n, K.outer.weight (y i.succ)
    exact Fin.prod_univ_succ _
  · funext y
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    change (∏ i : Fin (n + 1), (K.inner (y i)).weight (x i)) =
      (K.inner (y 0)).weight (x 0) *
        ∏ i : Fin n, (K.inner (y i.succ)).weight (x i.succ)
    exact Fin.prod_univ_succ _
  · funext x y a b
    apply Bool.eq_iff_iff.mpr
    change (decide (∀ i : Fin (n + 1), K.accepts (x i) (y i) (a i) (b i) = true) = true) ↔
      (K.accepts (x 0) (y 0) (a 0) (b 0) &&
        decide (∀ i : Fin n, K.accepts (x i.succ) (y i.succ) (a i.succ) (b i.succ) = true)) = true
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩
    · rintro ⟨hzero, hsucc⟩ i
      exact Fin.cases hzero hsucc i

theorem collisionValue_repetition_succ [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (n : Nat) :
    (K.repetition (n + 1)).collisionValue =
      (K.product (K.repetition n)).collisionValue := by
  rw [repetition_succ, collisionValue_reindex]

end
end MaxCutGames.Repetition.ProjectionKernel

/-!
The finite product algebra of dependency breaking.

Revealing one endpoint of each independently sampled question pair turns the
remaining question weight into a product of two separate functions, one for
each player. Further separate restrictions on the players' answers preserve
this product. The final theorem normalizes the displayed weights, rather than
assuming conditional independence as an abstract hypothesis.
-/

/-! Normalized local completion laws derived from their actual product weights.
Zero rows use explicit default laws and satisfy the same recombination identity.
-/

/-!
Every finite projection game has an exact conditional-kernel representation.
The right question uses its original marginal. Conditional left-question laws
are normalized original rows; zero rows use the original left marginal as a
fallback. Their zero outer weight makes the reconstruction identity valid on
all rows without positivity or support hypotheses.
-/

/-!
Alphabet-independent repetition of ordinary finite projection games.

The game is the actual finite question distribution and its local acceptance
predicate. The proof bounds nonnegative vector assignments by finite
thresholding and correlated sampling, factors each unrestricted product
strategy through that bound, and iterates the resulting collision contraction.
No repetition bound, decoder certificate, or alphabet-size budget is a premise.

The deterministic-predicate game interface permits arbitrary real question
weights. Distinct hidden constraints on the same question pair are not encoded
by this interface. Both v2 uses have a unique predicate for each question pair:
the distinct-position equation--variable game and the final simple graph.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineStateFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

/-- Optional continuation and labels use the existing subroutine semantics. -/
def statement (labels : Λ → Λ') (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    TM2.Stmt Γ Λ' (σ × τ) :=
  MachineSubroutine.statement labels exit (frameStatement q)

end MaxCutGames.Foundations.Complexity.MachineStateFrame

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFieldProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Preserved comparisons of actual field stacks and their finite equality profile.
All whole-word equalities below are specifications of finite-head comparison.
-/

namespace MaxCutGames.Foundations.Complexity.MachineFieldProfile

open Turing

theorem equalityProfile_encodeWord {q : Nat} (names : Fin q → Nat) (i j : Fin q) :
    equalityProfile (fun k => encodeWord (names k)) i j = decide (names i = names j) := by
  have h : encodeWord (names i) = encodeWord (names j) ↔ names i = names j := by
    constructor
    · intro heq
      have hh := congrArg List.length heq
      simpa only [encodeWord_length, Nat.add_right_cancel_iff] using hh
    · rintro heq
      rw [heq]
  simp only [equalityProfile, h]

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

omit [DecidableEq K] in
theorem statement_roundtrip (e : σ ≃ τ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ τ) :
    MachineControl.statement id e (MachineControl.statement id e.symm q) = q := by
  induction q <;> simp_all [MachineControl.statement]

end Transport

def setEntry {q : Nat} (profile : Profile q) (pair : Fin q × Fin q) (bit : Bool) : Profile q :=
  Function.update profile pair.1 (Function.update (profile pair.1) pair.2 bit)

theorem setEntry_apply {q : Nat} (profile : Profile q) (pair : Fin q × Fin q)
    (bit : Bool) (i j : Fin q) :
    setEntry profile pair bit i j = if (i, j) = pair then bit else profile i j := by
  rcases pair with ⟨a, b⟩
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [setEntry, hi, hj]

def setExpected {q : Nat} (words : Fin q → List Bool) (profile : Profile q)
    (pair : Fin q × Fin q) : Profile q :=
  setEntry profile pair (equalityProfile words pair.1 pair.2)

def foldProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) : Profile q := cells.foldl (setExpected words) initial

theorem foldProfile_apply {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (i j : Fin q) :
    foldProfile words initial cells i j =
      if (i, j) ∈ cells then equalityProfile words i j else initial i j := by
  induction cells generalizing initial with
  | nil => rfl
  | cons pair rest ih =>
    change foldProfile words (setExpected words initial pair) rest i j = _
    rw [ih]
    by_cases hrest : (i, j) ∈ rest
    · simp [hrest]
    · by_cases hpair : (i, j) = pair
      · subst pair
        simp [hrest, setExpected, setEntry_apply]
      · simp [hrest, hpair, setExpected, setEntry_apply]

def prefixProfile {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) : Profile q :=
  foldProfile words initial (cells.take r)

theorem prefixProfile_succ {q : Nat} (words : Fin q → List Bool) (initial : Profile q)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixProfile words initial cells (r + 1) =
      setExpected words (prefixProfile words initial cells r) cells[r] := by
  unfold prefixProfile foldProfile
  rw [List.take_succ_eq_append_getElem hr, List.foldl_append]
  rfl

theorem foldProfile_allPairs {q : Nat} (words : Fin q → List Bool) (initial : Profile q) :
    foldProfile words initial (allPairs q) = equalityProfile words := by
  funext i j
  simp [foldProfile_apply, mem_allPairs]

end MaxCutGames.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFiniteTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineFiniteTable

open Turing
open MaxCutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K] [DecidableEq σ]
variable {Γ : K → Type}

def dispatch (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) : List σ → TM2.Stmt Γ Λ σ
  | [] => next
  | key :: rest =>
      .branch (fun state => decide (state = key))
        (pushWord dst (table key).reverse next) (dispatch dst table next rest)

theorem stepAux_dispatch (dst : K) (table : σ → List (Γ dst))
    (next : TM2.Stmt Γ Λ σ) (keys : List σ) (state : σ)
    (hstate : state ∈ keys) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (dispatch dst table next keys) state tapes =
      TM2.stepAux next state (Function.update tapes dst (table state ++ tapes dst)) := by
  induction keys with
  | nil => simp at hstate
  | cons key rest ih =>
      by_cases h : state = key
      · subst state
        simp only [dispatch, TM2.stepAux, decide_true, Bool.cond_true]
        simpa only [List.reverse_reverse] using
          stepAux_pushWord dst (table key).reverse next key tapes
      · have hm : state ∈ rest := (List.mem_cons.mp hstate).resolve_left h
        simpa only [dispatch, TM2.stepAux, h, decide_false, Bool.cond_false] using ih hm

def emit (dst : K) (table : σ → List (Γ dst)) (keys : List σ)
    (next : TM2.Stmt Γ Λ σ) : TM2.Stmt Γ Λ σ :=
  dispatch dst table next keys

theorem stepAux_emit (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (hkeys : ∀ state, state ∈ keys) (next : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (emit dst table keys next) state tapes =
      TM2.stepAux next state (Function.update tapes dst (table state ++ tapes dst)) :=
  stepAux_dispatch dst table next keys state (hkeys state) tapes

/-- One actual transition emits the table entry and enters the continuation.
The caller supplies its program equation, not an execution assumption. -/
def emitInTime (dst : K) (table : σ → List (Γ dst))
    (keys : List σ) (hkeys : ∀ state, state ∈ keys)
    (program : Λ → TM2.Stmt Γ Λ σ) (label exitLabel : Λ)
    (atLabel : program label = emit dst table keys (.goto (fun _ => exitLabel)))
    (state : σ) (tapes : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some label, state, tapes⟩
      (some ⟨some exitLabel, state,
        Function.update tapes dst (table state ++ tapes dst)⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program label) state tapes) = _
    rw [atLabel, stepAux_emit dst table keys hkeys]
    rfl
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineFiniteTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegisterEmit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegisterEmit

open Turing
open MaxCutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

/-- The fixed literal push chain executes in one TM2 transition. -/
def emitStatement (destination : K) (offset : Nat) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  pushWord destination (List.replicate offset true) (finish exit)

theorem emitStep (destination : K) (offset : Nat) (emitLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atEmit : program emitLabel = emitStatement destination offset exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some emitLabel, (ambient, register), base⟩ =
      some ⟨exit, (ambient, register),
        Function.update base destination (List.replicate offset true ++ base destination)⟩ := by
  change some (TM2.stepAux (program emitLabel) (ambient, register) base) = _
  rw [atEmit, emitStatement, stepAux_pushWord]
  cases exit <;> simp [finish, TM2.stepAux]

theorem prefix_encodeWord (offset n : Nat) :
    List.replicate offset true ++ encodeWord n = encodeWord (offset + n) := by
  simp only [encodeWord, List.replicate_add, List.append_assoc]

end MaxCutGames.Foundations.Complexity.MachineRegisterEmit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Generator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Executable directed-dart tables for the fixed 64-label alphabet

The header gives vertex and dart counts. Every dart has one ordered row:
tail index, reverse-dart index, and 4096 Boolean predicate entries. Entry
`b + 64 * a` is the predicate at labels `(a,b)`. All fields, including bits
as 0/1 words, use the existing zero-delimited unary natural-word codec.

The decoder checks all index bounds, row counts, predicate lengths, reverse
involution, predicate transpose, and absence of trailing fields. Directed rows
preserve loops, self-reversing darts, and repeated constraint occurrences.
The size theorems concern the full encoded table, not a machine runtime.
-/

/-! Reversible regular port graphs and their actual finite walks. Vertices may
repeat; loops and parallel edges retain their distinct ports. The rotation
map sends an outgoing dart to its arrival dart and is an involution. -/

namespace MaxCutGames.Foundations.PCP.PoweringWalks

variable {V D : Type*}

theorem edgeAt_port (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      (edgeAt G n w k).2 = w.2 k := by
  intro n
  induction n with
  | zero =>
    intro w k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · exact ih (advanceTail G w) j

end MaxCutGames.Foundations.PCP.PoweringWalks

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

namespace MaxCutGames.Foundations.PCP.PortTables

open PoweringWalks

variable {n d : Nat}

theorem flatRows_valid (table : Table n d) : GraphTables.Valid (flatRows table) := by
  constructor
  · intro i
    simpa only [reverseAt_flatRows] using table.involutive i
  · intro i a b
    simpa only [reverseAt_flatRows, acceptsAt_flatRows] using table.transpose i a b

/-- Variable vertex count, with the port count fixed by the input family. -/
abbrev Input (ports : Nat) := (vertices : Nat) × Table vertices ports

end MaxCutGames.Foundations.PCP.PortTables

/-! A concrete constant-query proximity tester for a finite relation.

The proof oracle is a Boolean function on the Boolean functions on the finite
set of legal assignments. The tests are BLR linearity, self-corrected AND,
self-corrected unit, and comparison with a queried input coordinate.
The oracle's size depends exponentially on the number of legal assignments;
this is a fixed-relation construction, not a polynomial-size tester for an
arbitrary input formula. All tests below are explicit finite expectations.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ExpanderFamily
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype
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

namespace MaxCutGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

theorem size_le_mul {k : Nat} (hk : 0 < k) : size k ≤ growth * k := by
  by_cases hk1 : k = 1
  · subst k
    simpa [size, level] using growth_gt_one.le
  · have hk2 : 1 < k := by omega
    have hl : 0 < level k := Nat.clog_pos growth_gt_one hk2
    have hp : growth ^ (level k).pred < k :=
      Nat.pow_pred_clog_lt_self growth_gt_one hk2
    have he : (level k).pred + 1 = level k := Nat.succ_pred_eq_of_pos hl
    calc
      size k = growth ^ ((level k).pred + 1) := by rw [he]; rfl
      _ = growth * growth ^ (level k).pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ growth * k := Nat.mul_le_mul_left growth hp.le

end MaxCutGames.Foundations.PCP.ExpanderFamily

/-!
# Padding actual tail fibers to the geometric graph-family sizes

Every nonempty cloud is padded to the next family size. Empty clouds stay
empty, so their old vertices do not create new darts. Explicit equivalences
identify padded tail fibers and partition all darts by their original tails.
These facts give the global size bound without an expansion assumption.
-/

namespace MaxCutGames.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

/-- Every original dart occurs in exactly one cloud. -/
def dartCloudEquiv (G : ConstraintGraph V E A) : E ≃ Σ v : V, Cloud G v where
  toFun e := ⟨G.tail e, ⟨e, rfl⟩⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨e, he⟩⟩
    cases he
    rfl

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem sum_card_cloud (G : ConstraintGraph V E A) :
    (∑ v, Fintype.card (Cloud G v)) = Fintype.card E := by
  simpa only [Fintype.card_sigma] using (Fintype.card_congr (dartCloudEquiv G)).symm

end MaxCutGames.Foundations.PCP.CloudPadding

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

theorem vertexCount_eq (q n : Nat) : vertexCount q n = (q * q) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vertexCount, ih, pow_succ]

theorem vertexCount_positive {q : Nat} (hq : 0 < q) (n : Nat) :
    0 < vertexCount q n := by
  rw [vertexCount_eq]
  exact Nat.pow_pos (Nat.mul_pos hq hq)

end MaxCutGames.Foundations.PCP.ExpanderTables

namespace MaxCutGames.Foundations.PCP.PreprocessingLevels

/-- At most `fuel` continuing iterations can increment the exponent. -/
theorem levelLoop_level_le (g k fuel e s : Nat) :
    (levelLoop g k fuel e s).1 ≤ e + fuel := by
  induction fuel generalizing e s with
  | zero => simp only [levelLoop, Nat.add_zero, le_refl]
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · omega
      · have h := ih (e + 1) (s * g)
        omega

/-- The carried size remains the exact power of the carried exponent. -/
theorem levelLoop_power (g k fuel e : Nat) :
    (levelLoop g k fuel e (g ^ e)).2 =
      g ^ (levelLoop g k fuel e (g ^ e)).1 := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · rfl
      · simpa only [pow_succ] using ih (e + 1)

theorem levelLoop_covers (g k fuel e s : Nat) (hg : 1 < g)
    (hs : 0 < s) (hbudget : k ≤ s + fuel) :
    k ≤ (levelLoop g k fuel e s).2 := by
  induction fuel generalizing e s with
  | zero => simpa only [levelLoop, Nat.add_zero] using hbudget
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · assumption
      · apply ih
        · exact Nat.mul_pos hs (by omega)
        · have htwo : 2 ≤ g := by omega
          have hmul : s * 2 ≤ s * g := Nat.mul_le_mul_left s htwo
          omega

/-- The search never passes an exponent whose power already covers the
request. This remains true even without a sufficient fuel budget. -/
theorem levelLoop_le_of_covering_power (g k fuel e j : Nat)
    (he : e ≤ j) (hj : k ≤ g ^ j) :
    (levelLoop g k fuel e (g ^ e)).1 ≤ j := by
  induction fuel generalizing e with
  | zero => exact he
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · exact he
      · rename_i hnot
        have hne : e ≠ j := by
          intro h
          subst e
          exact hnot hj
        have hnext : e + 1 ≤ j := by omega
        simpa only [pow_succ] using ih (e + 1) hnext

end MaxCutGames.Foundations.PCP.PreprocessingLevels

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCloudCount

open Turing
open MachineComposition

variable {Λ σ : Type}

open MaxCutGames.Foundations.PCP

theorem rowsHits_eq_filter (v : Nat) (rs : List Row) :
    rowsHits v rs = (rs.filter (fun r => decide (r.1 = v))).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      by_cases h : r.1 = v <;> simp [rowsHits, h, ih, Nat.add_comm]

end MaxCutGames.Foundations.Complexity.MachineCloudCount

namespace MaxCutGames.Foundations.Complexity.MachineCeilingPower

open Turing
open MachineComposition
open MaxCutGames.Foundations.PCP

protected abbrev Tape.enumList : List Tape := [.input, .work, .power, .saved, .level, .fuel,
  .spare, .product]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

protected abbrev Label.enumList : List Label := [.init, .fuelFirst, .fuelSecond, .guard,
  .copyFirst, .copySecond, .compare, .restore, .decide, .scale, .transfer, .cleanup]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {σ : Type}

theorem coreTime_le (g k f p : Nat) :
    coreTime g k f p ≤ (f + 1) * roundBudget g k := by
  have hB : 3 ≤ roundBudget g k := by unfold roundBudget; omega
  induction f generalizing p with
  | zero => simpa only [coreTime, Nat.zero_add, Nat.one_mul] using hB
  | succ f ih =>
      rw [coreTime]
      by_cases h : k ≤ p
      · rw [ite_eq_left h]
        have hp := prefixTime_le_roundBudget g k p
        have hm := Nat.mul_le_mul_left (f + 1) hB
        have hc : f + 2 ≤ (f + 1) * roundBudget g k := by omega
        calc
          prefixTime k p + (f + 2) ≤ roundBudget g k + (f + 1) * roundBudget g k :=
            Nat.add_le_add hp hc
          _ = (f + 1 + 1) * roundBudget g k := by ring
      · rw [ite_eq_right h]
        have hb := continuingTime_le g k p (by omega)
        have hr := ih (p * g)
        calc
          prefixTime k p + ((p + g * p + 2) + coreTime g k f (p * g)) =
              (prefixTime k p + (p + g * p + 2)) + coreTime g k f (p * g) := by omega
          _ ≤ roundBudget g k + (f + 1) * roundBudget g k := Nat.add_le_add hb hr
          _ = (f + 1 + 1) * roundBudget g k := by ring

theorem totalTime_le (g k : Nat) : totalTime g k ≤ timeBound g k := by
  have h := coreTime_le g k k 1
  calc
    totalTime g k ≤ 1 + 2 * (k + 2) + (k + 1) * roundBudget g k :=
      Nat.add_le_add_left h _
    _ = timeBound g k := by unfold roundBudget timeBound; ring

end MaxCutGames.Foundations.Complexity.MachineCeilingPower

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual cloud counting, geometric padding, and unary subtraction

One finite program places the checked cloud counter and geometric search on
shared tapes. Its final phase physically subtracts the preserved cloud size
from the computed power. A head test handles the empty cloud separately.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCloudPadding

open Turing
open MachineComposition
open MaxCutGames.Foundations.PCP

/- Static placement of homogeneous tapes, with an explicit finite partial
inverse. Complement tapes are preserved by every simulated transition. -/
namespace Placement

variable {K K' Λ Λ' σ : Type}

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | some l => some (labels l)
  | none => exit

def configuration (view : K' → Option K) (labels : Λ → Λ') (exit : Option Λ')
    (extra : K' → List Bool) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K' => Bool) Λ' σ :=
  ⟨label labels exit c.l, c.var, tapes view c.stk extra⟩

variable [DecidableEq K] [DecidableEq K']

omit [DecidableEq K] [DecidableEq K'] in
theorem tapes_apply (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) :
    tapes view source extra (tape k) = source k := by
  simp only [tapes, left]

theorem tapes_update (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (source : K → List Bool) (extra : K' → List Bool) (k : K) (w : List Bool) :
    tapes view (Function.update source k w) extra =
      Function.update (tapes view source extra) (tape k) w := by
  funext j
  by_cases h : j = tape k
  · subst j
    simp [tapes, left]
  · cases hv : view j with
    | none => simp [tapes, hv, h]
    | some i =>
      have hi : i ≠ k := by
        intro hi
        subst i
        exact h (right j k hv).symm
      simp [tapes, hv, h, hi]

theorem stepAux_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (extra : K' → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (source : K → List Bool) :
    TM2.stepAux (statement tape labels exit q) state (tapes view source extra) =
      configuration view labels exit extra (TM2.stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, TM2.stepAux, tapes_apply tape view left]
    rw [← tapes_update tape view left right]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, TM2.stepAux, tapes_apply tape view left] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, TM2.stepAux, tapes_apply tape view left]
    rw [← tapes_update tape view left right]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih => simpa only [statement, TM2.stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases exit <;> rfl

theorem step_simulation (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit (source l))
    (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration view labels exit extra a) =
      some (configuration view labels exit extra b) := by
  cases a with
  | mk l state sourceTapes =>
    cases l with
    | none => simp [TM2.step] at h
    | some l =>
      have hb : TM2.stepAux (source l) state sourceTapes = b := Option.some.inj h
      rw [← hb]
      change some (TM2.stepAux (target (labels l)) state (tapes view sourceTapes extra)) = _
      rw [atLabels, stepAux_simulation tape view left right]

theorem trace (tape : K → K') (view : K' → Option K)
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Λ → Λ') (exit : Option Λ') (extra : K' → List Bool)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (target : Λ' → TM2.Stmt (fun _ : K' => Bool) Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement tape labels exit (source l))
    (n : Nat) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (run : (advance (TM2.step source))^[n] (some a) = some b) :
    (advance (TM2.step target))^[n]
      (some (configuration view labels exit extra a)) =
      some (configuration view labels exit extra b) :=
  liftSuccessfulTrace _ _ _
    (step_simulation tape view left right labels exit extra source target atLabels) n a b run

end Placement

inductive Label
  | init | countCode (l : MachineCloudCount.Label)
  | branch | powerCode (l : MachineCeilingPower.Label)
  | subtract | restore
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool

def countTape : MachineCloudCount.Tape → Tape
  | .original => .table
  | .target => .query
  | .count => .count
  | .work => .work
  | .scratch => .scratch
  | .spare => .spare

theorem countView_left (k : MachineCloudCount.Tape) : countView (countTape k) = some k := by
  cases k <;> rfl
theorem countView_right (j : Tape) (k : MachineCloudCount.Tape)
    (h : countView j = some k) : countTape k = j := by
  cases j <;> cases k <;> simp_all [countView, countTape]

def powerTape : MachineCeilingPower.Tape → Tape
  | .input => .count
  | .work => .work
  | .power => .power
  | .saved => .scratch
  | .level => .level
  | .fuel => .fuel
  | .spare => .spare
  | .product => .product

theorem powerView_left (k : MachineCeilingPower.Tape) : powerView (powerTape k) = some k := by
  cases k <;> rfl
theorem powerView_right (j : Tape) (k : MachineCeilingPower.Tape)
    (h : powerView j = some k) : powerTape k = j := by
  cases j <;> cases k <;> simp_all [powerView, powerTape]

theorem countTapes (a b c d e f : List Bool) (extra : Tape → List Bool) :
    Placement.tapes countView (MachineCloudCount.memory a d b e c f) extra =
      memory a b c d e f (extra .power) (extra .level) (extra .fuel) (extra .product) := by
  funext k; cases k <;> rfl

theorem powerTapes (c d g e h i f j : List Bool) (extra : Tape → List Bool) :
    Placement.tapes powerView (MachineCeilingPower.memory c d g e h i f j) extra =
      memory (extra .table) (extra .query) c d e f g h i j := by
  funext k; cases k <;> rfl

variable {σ : Type}

def subtractLoop : TM2.Stmt Alphabet Label (State σ) :=
  .pop .count (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.pop .power (fun state _ => (state.1, none))
        (.push .scratch (fun _ => true) (.goto fun _ => .subtract)))
      (.push .count (fun _ => false)
        (.load (fun state => (state.1, none)) (.goto fun _ => .restore))))

def postTime (k : Nat) : Nat :=
  1 + if k = 0 then 0 else MachineCeilingPower.totalTime ExpanderFamily.growth k + (2 * k + 2)

theorem postTime_le (k : Nat) :
    postTime k ≤ 1 + MachineCeilingPower.timeBound ExpanderFamily.growth k + (2 * k + 2) := by
  have h := MachineCeilingPower.totalTime_le ExpanderFamily.growth k
  unfold postTime
  split_ifs <;> omega

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C (ExpanderFamily.growth + 8) * Polynomial.X ^ 2 + 25 * Polynomial.X + 10

end MaxCutGames.Foundations.Complexity.MachineCloudPadding

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

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def internalDegree : Nat := Expanders.baseDegree * Expanders.baseDegree

end MaxCutGames.Foundations.PCP.PreprocessingRegularTables

/-!
# Executable whole-vertex padding of regular constraint tables

The first `n` vertex rows retain their old rotation and complete relation
tables. Every additional vertex has one self-reversing, always-accepting loop
at each port. An explicit finite sum equivalence identifies these stored rows
with `VertexPadding.pad`; rejection counts are preserved for every labeling.

The construction materializes finite vectors. No machine runtime bound is
claimed here.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingOffsets
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The executable dummy numbering is the sum of earlier cloud sizes plus
the local dummy index. This connects the actual list search in vertexOrder
with unary prefix-sum routines, without changing the chosen enumeration. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingOffsets

open PreprocessingRegularTables
open scoped BigOperators

theorem offset_all {n : Nat} (padding : Fin n → Nat) :
    offset padding n = ∑ v, padding v := by
  have ht : (List.finRange n).take n = List.finRange n := by simp
  unfold offset
  rw [ht, ← sigma_length padding (List.finRange n)]
  exact paddingList_length padding

end MaxCutGames.Foundations.PCP.PreprocessingPaddingOffsets

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCloudPrefix

open Turing MachineComposition
open MaxCutGames.Foundations.PCP
open scoped BigOperators

inductive Label
  | init | copyFirst | copySecond | guard | done
  | padding (l : MachineCloudPadding.Label)
  | add | clearCount | clearLevel | increment
  deriving DecidableEq, Fintype

variable {σ : Type}

/-- Uniform budget for one vertex iteration, including unary addition and
cleanup. Its input argument bounds the complete table length. -/
def cycleBudget (L : Nat) : Nat :=
  (ExpanderFamily.growth + 8) * (2 * L) ^ 2 + 25 * (2 * L) + 10 +
    (ExpanderFamily.growth + 2) * L + 5

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X *
      (Polynomial.C (ExpanderFamily.growth + 8) * (2 * Polynomial.X) ^ 2 +
        25 * (2 * Polynomial.X) + 10 +
          Polynomial.C (ExpanderFamily.growth + 2) * Polynomial.X + 5) +
    2 * (Polynomial.X + 1) + 3

end MaxCutGames.Foundations.Complexity.MachineCloudPrefix

namespace MaxCutGames.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

def appendTapes (source destination : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source destination base []
    (base destination ++ base source)

def firstTapes_inline_MachineAppendAt (destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt destination scratch base [] (base destination).reverse

def secondTapes_inline_MachineAppendAt (source destination scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch (firstTapes_inline_MachineAppendAt destination scratch base) []
    ((base source).reverse ++ (base destination).reverse)

end MaxCutGames.Foundations.Complexity.MachineAppendAt

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_SpectralCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual directed-cut expansion from the graph's zero-mean spectral
certificate. Parallel edges and loops retain their indexed port multiplicities. -/

/-!
An actual fixed-degree graph obtained by padding each outgoing-dart cloud to
the explicit expander family and then replacing vertices by cloud darts.
Expansion and majority rounding are proved dependencies, not hypotheses of
the final soundness theorem. Isolated original vertices have empty clouds.
-/

/-! Spectral contraction for the actual Boolean-flag lazy port graph. The
operator identity is proved in `PoweringLazy`; the estimate here averages the
elementary two-term square inequality. -/

noncomputable section

namespace MaxCutGames.Foundations.PCP.Preprocessing

open PoweringWalks SpectralReturn

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
  [DecidableEq V] [DecidableEq E] [DecidableEq A] [Nonempty E] [Nonempty A]

def degree : Nat := 2 * (2 * Expanders.baseDegree ^ 2 + 1)
def sizeFactor : Nat := ExpanderFamily.growth ^ 2 * degree

end MaxCutGames.Foundations.PCP.Preprocessing
end

/-!
# Concrete preprocessing table algorithm

Given one fixed expander base table, this function computes regularized
cloud rows, pads the whole vertex set, overlays a stored family table, and
adds the half-lazy rows. It is total even on zero-dart input tables. The
bounds below concern actual output data; an actual TM2 execution certificate
is a separate theorem and is not inferred from these size bounds.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingTables

open PreprocessingRegularTables

def degree : Nat := 2 * ((internalDegree + 1) + internalDegree)

end MaxCutGames.Foundations.PCP.PreprocessingTables

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

/-!
# Executable bounded port-address enumeration

For a port alphabet `Fin d`, the lists below enumerate every word of every
length at most the fixed radius. The resulting first-match selector searches
these addresses and never enumerates the ambient vertex type.
-/

/-!
# Executable integer encodings for the powering construction

All encodings below have explicit inverses. They use the arithmetic finite
function, sigma, and product equivalences rather than choosing enumerations
from cardinality proofs. Word digits use the head-major convention; addresses
are grouped by increasing word length. A dart is numbered first by its vertex,
then its word, with its two orientations adjacent.
-/

namespace MaxCutGames.Foundations.PCP.PoweringEnumeration

open PoweringLabels
open scoped BigOperators

theorem dartBlockEquiv_val (d n : Nat) (p : Fin (n + 1) → Fin d) (b : Bool) :
    (dartBlockEquiv d n (p, b)).val =
      2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (orientationEquiv b).val + 2 * (wordEquiv d (n + 1) p).val = _
  exact Nat.add_comm _ _

theorem dartEquiv_val (vertices d n : Nat) (b : Bool) (v : Fin vertices)
    (p : Fin (n + 1) → Fin d) :
    (dartEquiv vertices d n (b, (v, p))).val =
      (2 * d ^ (n + 1)) * v.val +
        2 * (wordEquiv d (n + 1) p).val + (orientationEquiv b).val := by
  change (dartBlockEquiv d n (p, b)).val + (2 * d ^ (n + 1)) * v.val = _
  rw [dartBlockEquiv_val]
  omega

def encodeDart (vertices d n : Nat) :
    (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) →
      Fin (2 * vertices * d ^ (n + 1)) := dartEquiv vertices d n

def decodeDart (vertices d n : Nat) :
    Fin (2 * vertices * d ^ (n + 1)) →
      (Bool × (Fin vertices × (Fin (n + 1) → Fin d))) := (dartEquiv vertices d n).symm

@[simp] theorem decodeDart_encodeDart (vertices d n : Nat)
    (e : Bool × (Fin vertices × (Fin (n + 1) → Fin d))) :
    decodeDart vertices d n (encodeDart vertices d n e) = e :=
  (dartEquiv vertices d n).symm_apply_apply e

@[simp] theorem encodeDart_decodeDart (vertices d n : Nat)
    (i : Fin (2 * vertices * d ^ (n + 1))) :
    encodeDart vertices d n (decodeDart vertices d n i) = i :=
  (dartEquiv vertices d n).apply_symm_apply i

end MaxCutGames.Foundations.PCP.PoweringEnumeration

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

open PoweringWalks PoweringLabels PoweringAddresses
open scoped BigOperators

variable {X A : Type*}

theorem firstIndex_matches (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) : p (xs.get (firstIndex p xs h)) := by
  rw [get_firstIndex]
  exact (scanWitness p xs h).property

/-- Every earlier stored address fails the matching predicate. -/
theorem firstIndex_is_first (p : X → Prop) [DecidablePred p] :
    ∀ (xs : List X) (h : ∃ a ∈ xs, p a) (j : Fin xs.length),
      j.val < (firstIndex p xs h).val → ¬p (xs.get j) := by
  intro xs
  induction xs with
  | nil => intro h; simp at h
  | cons a xs ih =>
    intro h j
    by_cases ha : p a
    · simp [firstIndex, ha]
    · refine Fin.cases (by intro _; exact ha) (fun i => ?_) j
      intro hi
      apply ih (match_in_tail_inline_PoweringOpinionTables p h ha) i
      exact Nat.lt_of_succ_lt_succ (by
        simpa only [firstIndex, ha, dite_false, Fin.val_succ] using hi)

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

/-!
# Executable tables of the actual powering graph

The input rotor and every base predicate are stored finite vectors. The output
has one row for each start vertex, bounded port word, and orientation, with the
two orientations adjacent. Every complete predicate table is generated from the
bounded first-address lookup test. Degree and walk length fix the output alphabet;
neither the alphabet nor an address list depends on the input vertex count.
-/

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
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Input
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

/-!
An actual fixed-alphabet TM2 parser for the complete Boolean relation table.
The finite syntax contains one slot reader for each of the `q*q` coordinates.
Each reader consumes `[false]` or `[true,false]`, stores the bit, and clears the
head register. No parser outcome or execution trace is an assumption.
-/

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

namespace MaxCutGames.Foundations.Complexity.MachineFixedBlockMap

open Turing

def emptyBuffer (N : Nat) : Buffer N := fun _ => false

end MaxCutGames.Foundations.Complexity.MachineFixedBlockMap

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Runtime2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every work tape of the actual alphabet-table machine stores Bool symbols.
This checks the work alphabets separately from the finite-machine structure's
input-alphabet condition, without changing the runtime certificate. -/

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem stepAux_transport_symm (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : τ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) state tapes =
      configuration e (stepAux q (e.symm state) tapes) := by
  simpa only [Equiv.apply_symm_apply] using
    stepAux_transport e q (e.symm state) tapes

end MaxCutGames.Foundations.Complexity.MachineStateEquiv

/-!
# Finite tape program for a powered relation row

The radius, address count, and powered alphabet size are fixed machine
parameters. The machine consumes live base predicate bits and endpoint-match
bits. Its finite register selects the first matching address, looks up the two
fixed powered labels, and conjoins the bounded list of base predicates.

Both input and output bits use the graph-table unary natural-word codec.
The theorems below describe actual TM2 transitions, not assumed execution
costs. Producing this input block from live graph rotor lookups is a separate
frontend composition obligation; no graph table occurs in the machine's
finite transition function.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition

/-! The outer construction uses independent finite registers for its existing
subprograms. This transport combines tape placement, an untouched register
frame, and a static register equivalence, without adding any machine steps. -/
namespace Lift

open MachineCloudPadding

variable {K K' Λ Λ' σ τ υ : Type}

def statement (tape : K → K') (labels : Λ → Λ') (exit : Option Λ')
    (registers : (σ × τ) ≃ υ) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2.Stmt (fun _ : K' => Bool) Λ' υ :=
  MachineStateEquiv.statement registers
    (MachineStateFrame.frameStatement (Placement.statement tape labels exit q))

def configuration (view : K' → Option K) (labels : Λ → Λ') (exit : Option Λ')
    (registers : (σ × τ) ≃ υ) (ambient : τ) (extra : K' → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) Λ σ) : TM2.Cfg (fun _ : K' => Bool) Λ' υ :=
  ⟨Placement.label labels exit c.l, registers (c.var, ambient),
    Placement.tapes view c.stk extra⟩

end Lift

end MaxCutGames.Foundations.Complexity.MachineRegularTable

namespace MaxCutGames.Foundations.Complexity.MachineCloudRank

open Turing MachineComposition MachineCloudCount

variable {σ : Type}

@[simp] theorem update_memory_spare (a b c d e f x : List Bool) :
    Function.update (memory a b c d e f) .spare x = memory a b c d e x := by
  funext k
  cases k <;> rfl

open MaxCutGames.Foundations.PCP

end MaxCutGames.Foundations.Complexity.MachineCloudRank

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularMetadata
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metadata preparation for an original regularized vertex. The
shared 27-tape row interface is preserved, with two explicit extra outputs
for padding count and geometric level. Family generation is a subsequent
stage and owns the rotor tape. -/

namespace MaxCutGames.Foundations.Complexity.MachineRegularMetadata

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

def rankTape : MachineCloudCount.Tape → Tape
  | .original => .inl 0
  | .work => .inl 10
  | .target => .inl 9
  | .scratch => .inl 11
  | .count => .inl 3
  | .spare => .inl 12

variable {σ : Type}

def rankView : Tape → Option MachineCloudCount.Tape
  | .inl i => match i.val with
    | 0 => some .original
    | 10 => some .work
    | 9 => some .target
    | 11 => some .scratch
    | 3 => some .count
    | 12 => some .spare
    | _ => none
  | .inr _ => none

theorem rankView_left (k : MachineCloudCount.Tape) : rankView (rankTape k) = some k := by
  cases k <;> rfl
theorem rankView_right (j : Tape) (k : MachineCloudCount.Tape)
    (h : rankView j = some k) : rankTape k = j := by
  cases j with
  | inl j => fin_cases j <;> simp_all [rankView, rankTape] <;> subst k <;> rfl
  | inr j => simp_all [rankView]

noncomputable def timePolynomial : Polynomial Nat :=
  (MachineCloudPrefix.timePolynomial + MachineCloudPadding.timePolynomial).comp
      (2 * Polynomial.X) + 40 * (Polynomial.X + 1)

end MaxCutGames.Foundations.Complexity.MachineRegularMetadata

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCloudSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual inverse cloud numbering. The input table and query are copied
preservingly. A unary working rank decreases only on equal stored tail
fields; a separate unary row position increases on every skipped row.
Only finite phase flags and symbol registers occur in the control state. -/

namespace MaxCutGames.Foundations.Complexity.MachineCloudSelect

open Turing MachineComposition
open MachineCloudCount (Row rowWords rowsHits )

abbrev BaseTape := MachineCloudCount.Tape

variable {σ : Type}

abbrev Tape := BaseTape ⊕ Unit

open MaxCutGames.Foundations.PCP

end MaxCutGames.Foundations.Complexity.MachineCloudSelect

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFixedDivMod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineFixedDivMod

open Turing
open Reduction.MachineSubstitution (pushWord stepAux_pushWord )

variable {K Λ σ : Type} [DecidableEq K]

theorem nextResidue_residue (d : Nat) (positive : 0 < d) (n : Nat) :
    nextResidue d positive (residue d positive n) = residue d positive (n + 1) := by
  apply Fin.ext
  change (n % d + 1) % d = (n + 1) % d
  simp only [Nat.add_mod, Nat.mod_mod]

/-- Each emitter is a fixed finite statement indexed by one of the `d` residues. -/
def emitter (d : Nat) (positive : 0 < d) (remainder : K) (exit : Option Λ)
    (r : Fin d) : TM2.Stmt (Alphabet (K := K)) Λ (State σ d) :=
  pushWord remainder (List.replicate r.val true)
    (.load (fun state => ((state.1.1, residue d positive 0), none))
      (Reduction.MachineTransfer.exitAt remainder exit))

theorem update_source_inline_MachineFixedDivMod (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      source replacement = tapes source quotient remainder base replacement quotientWord remainderWord := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [tapes, MachineCopy.forkTapes, sourceQuotient, sourceRemainder]
  · by_cases hq : k = quotient
    · subst k
      simp [tapes, MachineCopy.forkTapes, Ne.symm sourceQuotient, quotientRemainder]
    · by_cases hr : k = remainder
      · subst k
        simp [tapes, MachineCopy.forkTapes, Ne.symm sourceRemainder]
      · simp [tapes, MachineCopy.forkTapes, hs, hq, hr]

theorem update_quotient_inline_MachineFixedDivMod (source quotient remainder : K)
    (quotientRemainder : quotient ≠ remainder) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      quotient replacement = tapes source quotient remainder base input replacement remainderWord := by
  funext k
  by_cases hq : k = quotient
  · subst k
    simp [tapes, MachineCopy.forkTapes, quotientRemainder]
  · by_cases hr : k = remainder
    · subst k
      simp [tapes, MachineCopy.forkTapes, Ne.symm quotientRemainder]
    · simp [tapes, MachineCopy.forkTapes, hq, hr]

theorem update_remainder_inline_MachineFixedDivMod (source quotient remainder : K) (base : K → List Bool)
    (input quotientWord remainderWord replacement : List Bool) :
    Function.update (tapes source quotient remainder base input quotientWord remainderWord)
      remainder replacement = tapes source quotient remainder base input quotientWord replacement := by
  simp [tapes, MachineCopy.forkTapes]

theorem scanAux_true (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (base : K → List Bool) (input quotientWord remainderWord : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.stepAux (scanLoop d positive source quotient scanLabel emitterLabel)
      ((ambient, r), register)
      (tapes source quotient remainder base (true :: input) quotientWord remainderWord) =
      ⟨some scanLabel, ((ambient, nextResidue d positive r), some true),
        tapes source quotient remainder base input
          (if (nextResidue d positive r).val = 0 then true :: quotientWord else quotientWord)
          remainderWord⟩ := by
  by_cases hcarry : (nextResidue d positive r).val = 0 <;>
    simp [scanLoop, TM2.stepAux, sourceQuotient, sourceRemainder, quotientRemainder,
      update_source_inline_MachineFixedDivMod, update_quotient_inline_MachineFixedDivMod, hcarry]

theorem scanAux_false (d : Nat) (positive : 0 < d) (source quotient remainder : K)
    (sourceQuotient : source ≠ quotient) (sourceRemainder : source ≠ remainder)
    (quotientRemainder : quotient ≠ remainder) (scanLabel : Λ) (emitterLabel : Fin d → Λ)
    (base : K → List Bool) (input quotientWord remainderWord : List Bool)
    (ambient : σ) (r : Fin d) (register : Option Bool) :
    TM2.stepAux (scanLoop d positive source quotient scanLabel emitterLabel)
      ((ambient, r), register)
      (tapes source quotient remainder base (false :: input) quotientWord remainderWord) =
      ⟨some (emitterLabel r), ((ambient, r), some false),
        tapes source quotient remainder base (false :: input) quotientWord remainderWord⟩ := by
  simp [scanLoop, TM2.stepAux, sourceQuotient, sourceRemainder, quotientRemainder,
    update_source_inline_MachineFixedDivMod]

end MaxCutGames.Foundations.Complexity.MachineFixedDivMod

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

protected abbrev Tape.enumList : List Tape := [.inputVertex, .table, .output, .emitScratch,
  .queryReverse, .queryIndex, .lookupOutput, .lookupWork, .lookupRestore, .quotientFirst,
  .quotientSecond, .remainderFirst, .remainderSecond]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

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

theorem controlStatement_inverse_inline_MachineExpanderRowDivision {K Λ σ τ : Type} {Γ : K → Type}
    (e : σ ≃ τ) (q : TM2.Stmt Γ Λ σ) :
    MachineControl.statement id e.symm (MachineControl.statement id e q) = q := by
  induction q <;>
    simp_all only [MachineControl.statement, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, id_eq]

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

protected abbrev ExtraTape.enumList : List ExtraTape := [.vertexCount, .result]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

protected abbrev OuterLabel.enumList : List OuterLabel := [.initialize_, .vertexGuard,
  .prepareRow, .afterRow, .reverseOutput, .done]

protected theorem OuterLabel.enumList_nodup : OuterLabel.enumList.Nodup := by decide

instance instFintypeOuterLabel : Fintype OuterLabel where
  elems := ⟨OuterLabel.enumList, OuterLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

protected abbrev ExtraTape.enumList : List ExtraTape := [.remainingLevel, .currentSize,
  .unaryScratch, .tableReverse]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

/-! Static, pointwise Boolean presentation of the actual family tape alphabet.
Every conversion below is an identity on symbols and has no machine runtime. -/

/-!
# Actual family-table installation and counter cleanup

Checked physical drain and transfer loops are placed in the family program
through its finite register equivalence. Alphabet equality transports their
actual traces back to the dependent alphabet of the full family machine.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

theorem controlStatementInverse {K Λ σ τ : Type} {Γ : K → Type}
    (states : σ ≃ τ) (q : TM2.Stmt Γ Λ σ) :
    MachineControl.statement id states.symm (MachineControl.statement id states q) = q := by
  induction q <;>
    simp_all only [MachineControl.statement, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, id_eq]

/-- Static state-coordinate transport preserves every actual transition. -/
theorem controlTrace {K Λ σ τ : Type} {Γ : K → Type} [DecidableEq K]
    (states : σ ≃ τ) (target : Λ → TM2.Stmt Γ Λ τ)
    (n : Nat) (start finish : TM2.Cfg Γ Λ σ)
    (run : (advance (TM2.step (MachineControl.program (Equiv.refl Λ) states.symm target)))^[n]
      (some start) = some finish) :
    (advance (TM2.step target))^[n]
      (some (MachineControl.configuration id states start)) =
      some (MachineControl.configuration id states finish) := by
  let source := MachineControl.program (Equiv.refl Λ) states.symm target
  have roundtrip : MachineControl.program (Equiv.refl Λ) states source = target := by
    funext label
    change MachineControl.statement id states
      (MachineControl.statement id states.symm (target label)) = target label
    exact controlStatementInverse states.symm _
  have simulation : ∀ a b, TM2.step source a = some b →
      TM2.step target (MachineControl.configuration id states a) =
        some (MachineControl.configuration id states b) := by
    intro a b hab
    have h := MachineControl.step_simulation (Equiv.refl Λ) states source a
    rw [roundtrip, hab] at h
    exact h
  exact liftSuccessfulTrace (TM2.step source) (TM2.step target)
    (MachineControl.configuration id states) simulation n start finish run

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

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

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

/-!
# Complete finite machine execution for the next expander table

The initialized old table and unary vertex count are consumed by one actual
finite program. The machine writes precisely the complete square/zigzag
rotation table, preserving its old table and all promised framing. The bound
is quadratic in the unary old-table length for each fixed small graph.
-/

/-!
# Bounds for materializing the actual expander family

The costs use the encoded old and new rotation tables, and the already checked
table-machine polynomial. The finite sum follows the actual recursive table
family. These arithmetic lemmas introduce no execution assumptions and make no
claim that the output is polynomial in an isolated binary level parameter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds

open PCP.ExpanderTables PCP.ExpanderRowControl

theorem vertexCount_monotone {q : Nat} (positive : 0 < q) :
    Monotone (vertexCount q) := by
  intro m n hmn
  rw [vertexCount_eq, vertexCount_eq]
  exact Nat.pow_le_pow_right (Nat.mul_pos positive positive) hmn

theorem level_le_vertexCount {q : Nat} (growth : 1 < q * q) (level : Nat) :
    level ≤ vertexCount q level := by
  have positive : 0 < q := by nlinarith
  induction level with
  | zero => exact Nat.zero_le _
  | succ level ih =>
    have hpos := vertexCount_positive positive level
    have hmul := Nat.mul_le_mul_left (vertexCount q level)
      (show 2 ≤ q * q by omega)
    change level + 1 ≤ vertexCount q level * (q * q)
    nlinarith

end MaxCutGames.Foundations.Complexity.MachineExpanderFamilyBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePaddedExpanderFamilyBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryLessAt

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K]

def statement (slots : Fin 4 ↪ K) (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State σ)
  | .scan => scan slots (labels .scan) (labels .restoreLeft)
  | .restoreLeft => Reduction.MachineTransfer.loopAt (slots 2) (slots 0) id false
      (labels .restoreLeft) (some (labels .restoreRight))
  | .restoreRight => Reduction.MachineTransfer.loopAt (slots 3) (slots 1) id false
      (labels .restoreRight) exit

end MaxCutGames.Foundations.Complexity.MachineUnaryLessAt

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineDummyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite control for the dummy self-loop rows of one padded vertex.
The port count is a fixed program parameter. Vertex and reverse-dart indices
remain on unary tapes, and each row advances the reverse index by one actual
push. The all-true relation is a fixed literal field, initialized once.
-/

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

namespace MaxCutGames.Foundations.Complexity.MachinePaddingRows

open Turing MachineComposition

abbrev Alphabet : Tape → Type := MachineEmbedding.Alphabet
  (fun _ : Fin 6 => Bool) (fun _ : Unit => Bool)

end MaxCutGames.Foundations.Complexity.MachinePaddingRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingWords

open Complexity PortTables

variable {n m d : Nat}

/-- Mixed-radix row order is vertex-major, then increasing port order. -/
theorem flatten_ofFn_rowIndex {α : Type*} (f : Fin (n * d) → List α) :
    (List.ofFn f).flatten =
      (List.ofFn (fun v : Fin n =>
        (List.ofFn (fun p : Fin d => f (rowIndex n d (v, p)))).flatten)).flatten := by
  rw [List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext v
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val, Nat.mul_comm, Nat.add_comm]

end MaxCutGames.Foundations.PCP.PreprocessingPaddingWords

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularVertexBlock
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regularized vertex-block execution

The finite internal-port loop invokes the checked row machine for every port in
order. Each invocation restores the shared 27-tape frame. Inherited-row stages
use fixed tape placements and finite state permutations.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

open Turing MachineComposition PCP MachineRegularInternalRow
open PreprocessingCloudIndex PreprocessingRegularTables

variable {σ Λ : Type}

theorem portBits_eq {q : Nat} (bits : Fin q → List Bool) (k : Nat) (hk : k ≤ q) :
    portBits bits k = (List.ofFn (fun p : Fin k => bits ⟨p.val, lt_of_lt_of_le p.isLt hk⟩)).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : k < q := by omega
    rw [portBits, dite_eq_left h, ih (by omega), List.ofFn_succ_last, List.flatten_append]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl

theorem portBits_all {q : Nat} (bits : Fin q → List Bool) :
    portBits bits q = (List.ofFn bits).flatten := by
  simpa only [Fin.eta] using portBits_eq bits q (Nat.le_refl q)

end MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularLoopWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prefix and suffix invariants for regular-table row loops

These finite block identities apply to original-vertex blocks, to dummy blocks
within an owner, and to whole owner blocks. They expose exactly the next emitted
block while preserving the codec's established order.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularLoopWords

@[simp] theorem blocksSuffix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f 0 = (List.ofFn f).flatten := by
  simp only [blocksSuffix, List.drop_zero]

@[simp] theorem blocksSuffix_all {n : Nat} (f : Fin n → List Bool) :
    blocksSuffix f n = [] := by
  have h : (List.ofFn f).drop n = [] := by
    simpa only [List.length_ofFn] using (List.drop_length (l := List.ofFn f))
  exact congrArg List.flatten h

/-- The completed and remaining portions partition the original bitstream. -/
theorem blocksPrefix_append_suffix {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    blocksPrefix f k ++ blocksSuffix f k = (List.ofFn f).flatten := by
  unfold blocksPrefix blocksSuffix
  rw [← List.flatten_append, List.take_append_drop]

end MaxCutGames.Foundations.PCP.PreprocessingRegularLoopWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOwnerProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

theorem oneStep_inline_MachineRegularOwnerBody {A : Type} {f : A → Option A} {a b : A}
    (h : f a = some b) : (advance f)^[1] (some a) = some b := by
  simpa only [Function.iterate_one, advance_some] using h

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open MaxCutGames.Foundations.Complexity
open scoped BigOperators

noncomputable def regularPolynomial : Polynomial Nat :=
  tablePolynomial ExpanderFamily.growth (ExpanderFamily.growth * (internalDegree + 1))

noncomputable def rotorPolynomial (q : Nat) : Polynomial Nat :=
  (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X) *
    (Polynomial.C (ExpanderFamily.growth * q) * Polynomial.X + 1)

end MaxCutGames.Foundations.PCP.PreprocessingMachineBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

namespace Header

instance instFintypeExtra : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {σ : Type}

noncomputable def arithmeticPolynomial (q : Nat) : Polynomial Nat :=
  let X : Polynomial Nat := Polynomial.X
  let G : Polynomial Nat := Polynomial.C ExpanderFamily.growth * X
  let D : Polynomial Nat := Polynomial.C (ExpanderFamily.growth * (q + 1)) * X
  (12 * X + 11) + ((2 * (X + 2) + (G + 1)) + (2 * (G + 1) + 1)) +
    (((2 * (D + 2) + 2 * (G + 2)) + (2 * ((G + D + 2) + X) + 3)) + 1 + (X + 1) + 1)

noncomputable def timePolynomial (q : Nat) : Polynomial Nat :=
  MachineCloudPrefix.timePolynomial.comp (2 * Polynomial.X + 1) + arithmeticPolynomial q

end Header

end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePortReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachinePortReindex

open Turing MachineComposition
open Reduction.MachineSubstitution (pushWord stepAux_pushWord)

variable {K Λ A : Type} [DecidableEq K]

def frame_inline_MachinePortReindex (tape : Fin 5 → K) (base : K → List Bool)
    (work quotient output : List Bool) : K → List Bool :=
  MachineCopy.forkTapes (tape 2) (tape 3) (tape 4) base work quotient output

end MaxCutGames.Foundations.Complexity.MachinePortReindex

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingLazyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact codec expansion of the executable lazy graph table. Each vertex
contributes its `d` always-accepting selfloops, followed by its `d` stored
constraints with the reverse field changed by the displayed div/mod map. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingLazyWords

open PortTables GraphTables PreprocessingOverlayTables
open MaxCutGames.Foundations.Complexity

variable {n d : Nat}

def trueRelation : RelationTable := Vector.replicate 4096 true

theorem relationWords_true : relationWords trueRelation = List.replicate 4096 1 := by
  simp only [relationWords, trueRelation, Vector.toList_replicate,
    List.map_replicate, bitWord, ite_true, if_true]

/-- Finite mixed-radix indexing agrees with the actual row-vector order. -/
theorem ofFn_rowIndex {α : Type*} (f : Fin (n * d) → α) :
    List.ofFn f = (List.ofFn fun v : Fin n =>
      List.ofFn fun p : Fin d => f (rowIndex n d (v, p))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  congr 1
  funext v
  congr 1
  funext p
  apply congrArg f
  apply Fin.ext
  simp only [rowIndex_val]
  ac_rfl

end MaxCutGames.Foundations.PCP.PreprocessingLazyWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingOverlayWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact stored-row and codec expansion of the executable overlay. Within
each vertex block, all original ports precede all expander ports. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingOverlayWords

open PortTables GraphTables PreprocessingOverlayTables
open Complexity

variable {n d e : Nat}

abbrev trueRelation := PreprocessingLazyWords.trueRelation

end MaxCutGames.Foundations.PCP.PreprocessingOverlayWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineCanonicalOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Canonical output for finite Boolean machines

A raw machine may halt with retained metadata and a changed finite state.
This wrapper redirects its halt to a fixed list of actual tape drains, then
executes one state-reset instruction. The output tape is preserved and the
result is literally `haltList`. Its cost follows from the raw execution and
the maximum number of pushes in a raw statement.

The cleanup list is fixed with the program, not selected from the input.
It may contain repetitions and may be empty when output is the only tape.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCanonicalOutput

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

abbrev Label (Λ : Type) (chosen : List K) := Λ ⊕ (MachineDrainMany.Label chosen ⊕ Unit)

def cleanupLabel (chosen : List K) : MachineDrainMany.Label chosen → Label Λ chosen :=
  fun label => .inr (.inl label)

def resetLabel (chosen : List K) : Label Λ chosen := .inr (.inr ())

def cleanupEntry (chosen : List K) : Option (Label Λ chosen) :=
  MachineDrainMany.entry chosen (cleanupLabel chosen) (some (resetLabel chosen))

end MaxCutGames.Foundations.Complexity.MachineCanonicalOutput

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual output prefixes used by the regularization loops.
The bounds include the stored headers and all earlier original/owner blocks.
They concern actual serialized words; machine executions are proved separately. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularLoopWords
open MaxCutGames.Foundations.Complexity
open scoped BigOperators

theorem blocksPrefix_length_le {n : Nat} (f : Fin n → List Bool) (k : Nat) :
    (blocksPrefix f k).length ≤ (List.ofFn f).flatten.length := by
  have h := congrArg List.length (blocksPrefix_append_suffix f k)
  simp only [List.length_append] at h
  omega

end MaxCutGames.Foundations.PCP.PreprocessingRegularBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/
namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds MachineRegularOriginalBody

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X
noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192
noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + Polynomial.C q * rowPolynomial q
noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)
noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+20)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40995)
noncomputable def cleanupPolynomial (q : Nat) : Polynomial Nat := 6*wide + rotorPolynomial q + 13

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.originalTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.originalTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularOriginalClean.timeBound, MachineRegularVertexBlock.rowSizeBound]
  ring

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

noncomputable def wide : Polynomial Nat := Polynomial.C (ExpanderFamily.growth + 1) * Polynomial.X

noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  wide + wide * Polynomial.C (q + 1) + 8192

noncomputable def outputPolynomial (q : Nat) : Polynomial Nat :=
  wide + regularPolynomial + Polynomial.C q * rowPolynomial q

noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10*wide + 2*wide + 13*wide + 5*wide +
    Polynomial.C (5*q+10)*(wide+wide) + 4*wide + 2*outputPolynomial q +
      Polynomial.C (8*q+41066)

noncomputable def blockPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C q * corePolynomial q + Polynomial.C (5*q+11)*wide +
    2*outputPolynomial q + Polynomial.C (5*q+40986)

theorem blockPolynomial_eval (q L : Nat) :
    (blockPolynomial q).eval L =
      MachineRegularVertexBlock.dummyTimeBound q
        ((ExpanderFamily.growth+1)*L) ((rotorPolynomial q).eval L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        ((ExpanderFamily.growth+1)*L) ((ExpanderFamily.growth+1)*L)
        (((ExpanderFamily.growth+1)*L) + regularPolynomial.eval L)
        ((ExpanderFamily.growth+1)*L) := by
  simp only [blockPolynomial, corePolynomial, outputPolynomial, rowPolynomial, wide,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_ofNat, MachineRegularVertexBlock.dummyTimeBound,
    MachineRegularVertexBlock.portTimeBound, MachineRegularInternalRow.coreTimeBound,
    MachineRegularDummyRow.timeBound, MachineRegularVertexBlock.rowSizeBound]
  simp only [Nat.add_assoc]

noncomputable def prePolynomial : Polynomial Nat :=
  MachineCloudPadding.timePolynomial.comp (2*Polynomial.X+1) + 4*wide + 6

noncomputable def loopPolynomial : Polynomial Nat :=
  wide * (blockPolynomial internalDegree + 2)

noncomputable def cleanupPolynomial : Polynomial Nat :=
  6*wide + rotorPolynomial internalDegree + 13

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A fixed five-tape machine physically copies a graph table, preserves the
original input, and splits its two unary header fields from the copied rows.
The exact trace is ambient-state polymorphic for static machine placement.
-/

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

/-! Exact table-codec endpoint of the polynomial padding-row routine.
The caller supplies the physical unary counters and copied old-row buffer
with the updated headers. This theorem executes every added row and proves
that the resulting output is exactly the existing full table encoding. -/

/-!
# Vertex padding from the original serialized port graph

Header counters, the geometric padding count, and the initial row buffer
are generated by physical tape operations before the checked row emitter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineVertexPadding

open Turing MachineComposition
open MaxCutGames.Foundations.PCP
open MachineCloudPadding

theorem rowAlphabet_eq : MachinePaddingRows.Alphabet = (fun _ : MachinePaddingRows.Tape => Bool) := by
  funext k; cases k <;> rfl

def rowBoolTapes (base : (k : MachinePaddingRows.Tape) → List (MachinePaddingRows.Alphabet k)) :
    MachinePaddingRows.Tape → List Bool
  | .inl k => base (.inl k)
  | .inr k => base (.inr k)

def intermediateCoefficient (d : Nat) : Nat := (d + 2) * ExpanderFamily.growth + 8

noncomputable def intermediatePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (intermediateCoefficient d) * (Polynomial.X + 1)

noncomputable def otherPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (ExpanderFamily.growth + 8) * (Polynomial.X + 1) ^ 2 +
    Polynomial.C ((d + 8) * ExpanderFamily.growth + 24) * (Polynomial.X + 1) + 8222

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  otherPolynomial d + (MachinePaddingCertificate.timePolynomial d).comp (intermediatePolynomial d)

end MaxCutGames.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachinePaddedOverlay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical composition of vertex padding, expander generation, and overlay

The level produced by vertex padding is the family machine's actual input
stack. The two resulting archives are the overlay machine's actual archive
stacks. Static tape placement and finite-state framing preserve the original
input; no copying or recomputation is hidden in a phase boundary.
-/

namespace MaxCutGames.Foundations.Complexity.MachinePaddedOverlay

open Turing MachineComposition MachineCloudPadding
open PCP

variable {d : Nat}

abbrev baseDegree := Expanders.baseDegree
abbrev overlayDegree := PreprocessingRegularTables.internalDegree

/-- The actual padded vertex count is linear in the original encoded size. -/
noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C ExpanderFamily.growth * (Polynomial.X + 1)

/-- Full unary lengths of both physical archives, including all graph
predicate entries, all delimiters, and all expander reverse addresses. -/
noncomputable def archivePolynomial (d : Nat) : Polynomial Nat :=
  let s := sizePolynomial
  s + s * Polynomial.C d + 2 +
    (s * Polynomial.C d) * (s + s * Polynomial.C d + 8192) +
    (s * Polynomial.C overlayDegree) * (s * Polynomial.C overlayDegree + 1)

end MaxCutGames.Foundations.Complexity.MachinePaddedOverlay

/-! Exact dummy-block codec used by the complete lazy-table machine. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTableRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

/-! The actual padding, expander overlay, and lazy-loop stages composed into
one polynomial-time finite machine. The initial degree-replacement stage is
assembled separately. -/

/-! The complete actual preprocessing machine, including degree replacement,
vertex padding, explicit expander construction, overlay, and lazy edges. -/

/-!
An actual logarithmic-round counter. Unary input is stripped to a raw tally;
each positive round emits one tally and halves the remaining input by pairing
symbols. The zero input emits one round explicitly. All tapes except the
canonical output are empty at termination.
-/

namespace MaxCutGames.Foundations.Complexity.MachineLogCounter

open Turing

theorem bitLength_half {n : Nat} (h : n ≠ 0) : bitLength n = bitLength (n / 2) + 1 := by
  by_cases hone : n = 1
  · subst n; rfl
  have hn : 2 ≤ n := by omega
  have hh : n / 2 ≠ 0 := by omega
  rw [bitLength_positive h, bitLength_positive hh, Nat.log2_def n, ite_eq_left hn]

theorem increments_half {n : Nat} (h : n ≠ 0) (started : Bool) :
    increments n started = increments (n / 2) true + 1 := by
  rw [increments, ite_eq_right h, increments_true, bitLength_half h]

def program : Fin 5 → TM2.Stmt Alphabet (Fin 5) State
  | 0 => .push 2 (fun _ => false) (.goto fun _ => 1)
  | 1 => stripLoop
  | 2 => guardLoop
  | 3 => halfLoop
  | 4 => Reduction.MachineTransfer.loopAt 1 0 id false 4 (some 2)

def machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := Fin 5
  main := 0
  σ := State
  initialState := initialState
  m := program

def configuration (label : Option (Fin 5)) (state : State)
    (input scratch output : List Bool) : machine.Cfg :=
  ⟨label, state, rawTapes input scratch output⟩

def next := MachineComposition.advance machine.step

theorem stripStep_true (input scratch output : List Bool) (state : State) :
    machine.step (configuration (some 1) state (true :: input) scratch output) =
      some (configuration (some 1) (state.1, some true) input (true :: scratch) output) := by
  change some (TM2.stepAux stripLoop state (rawTapes (true :: input) scratch output)) = _
  simp [stripLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter, update_scratch_inline_MachineLogCounter]
  rfl

theorem stripStep_false (scratch output : List Bool) (state : State) :
    machine.step (configuration (some 1) state [false] scratch output) =
      some (configuration (some 4) initialState [] scratch output) := by
  change some (TM2.stepAux stripLoop state (rawTapes [false] scratch output)) = _
  simp [stripLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter]
  rfl

theorem halfStep_nil (scratch output : List Bool) (parity started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((parity, started), register) [] scratch output) =
      some (configuration (some 4) ((false, started), none) [] scratch output) := by
  change some (TM2.stepAux halfLoop ((parity, started), register) (rawTapes [] scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter]
  rfl

theorem halfStep_false (input scratch output : List Bool) (started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((false, started), register) (true :: input) scratch output) =
      some (configuration (some 3) ((true, started), some true) input scratch output) := by
  change some (TM2.stepAux halfLoop ((false, started), register)
    (rawTapes (true :: input) scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter]
  rfl

theorem halfStep_true (input scratch output : List Bool) (started : Bool) (register : Option Bool) :
    machine.step (configuration (some 3) ((true, started), register) (true :: input) scratch output) =
      some (configuration (some 3) ((false, started), some true) input (true :: scratch) output) := by
  change some (TM2.stepAux halfLoop ((true, started), register)
    (rawTapes (true :: input) scratch output)) = _
  simp [halfLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_input_inline_MachineLogCounter, update_scratch_inline_MachineLogCounter]
  rfl

/-- A parity bit implements division by two using actual pop/push transitions. -/
theorem halfTrace (n m : Nat) (output : List Bool) (parity started : Bool)
    (register : Option Bool) :
    next^[n + 1] (some (configuration (some 3) ((parity, started), register)
      (List.replicate n true) (List.replicate m true) output)) =
      some (configuration (some 4) ((false, started), none) []
        (List.replicate (m + (n + if parity then 1 else 0) / 2) true) output) := by
  induction n generalizing m parity register with
  | zero =>
    cases parity <;>
      simpa only [Nat.zero_add, Function.iterate_one, next, MachineComposition.advance_some,
        List.replicate_zero, Bool.false_eq_true, ite_false, ite_true, if_true, Nat.zero_div,
        Nat.add_zero, Nat.reduceDiv] using
        halfStep_nil (List.replicate m true) output _ started register
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change next^[n + 1]
      (machine.step (configuration (some 3) ((parity, started), register)
        (true :: List.replicate n true) (List.replicate m true) output)) = _
    cases parity with
    | false =>
      rw [halfStep_false, ih]
      congr 2
    | true =>
      rw [halfStep_true]
      change next^[n + 1] (some (configuration (some 3) ((false, started), some true)
        (List.replicate n true) (List.replicate (m + 1) true) output)) = _
      rw [ih]
      congr 2
      congr 1
      change m + 1 + n / 2 = m + (n + 1 + 1) / 2
      omega

theorem guardStep_zero (output : List Bool) (started : Bool) :
    machine.step (configuration (some 2) ((false, started), none) [] [] output) =
      some (configuration none initialState [] [] (if started then output else true :: output)) := by
  change some (TM2.stepAux guardLoop ((false, started), none) (rawTapes [] [] output)) = _
  cases started <;> simp [guardLoop, TM2.stepAux, rawTapes, configuration]
  all_goals try rw [update_output_inline_MachineLogCounter]
  all_goals rfl

theorem guardStep_positive (n : Nat) (output : List Bool) (started : Bool) :
    machine.step (configuration (some 2) ((false, started), none)
      (List.replicate (n + 1) true) [] output) =
      some (configuration (some 3) ((false, true), none)
        (List.replicate (n + 1) true) [] (true :: output)) := by
  change some (TM2.stepAux guardLoop ((false, started), none)
    (rawTapes (true :: List.replicate n true) [] output)) = _
  simp [guardLoop, TM2.stepAux, rawTapes, configuration]
  rw [update_output_inline_MachineLogCounter]
  simp only [List.replicate_succ]
  rfl

theorem initList_eq (input : List Bool) :
    initList machine input = configuration (some 0) initialState input [] [] := by
  simp only [machine]
  unfold initList configuration
  congr 1
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = configuration none initialState [] [] output := by
  unfold haltList configuration
  congr 1
  funext k
  change Fin 3 at k
  fin_cases k <;> rfl

theorem initialStep (input : List Bool) :
    machine.step (configuration (some 0) initialState input [] []) =
      some (configuration (some 1) initialState input [] [false]) := by
  change some (TM2.stepAux (.push (2 : Fin 3) (fun _ : State => false) (.goto fun _ => (1 : Fin 5)))
    initialState (rawTapes input [] [])) = _
  simp only [TM2.stepAux, rawTapes]
  rw [update_output_inline_MachineLogCounter]
  rfl

end MaxCutGames.Foundations.Complexity.MachineLogCounter

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_GraphCounterFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cleanup and emission of the counter followed by the preserved graph. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterFinish

open Turing GraphCounterModel

theorem start_eq (counter rest original : List Bool) :
    clockConfiguration (extraTapes rest original) none
      (haltList MachineLogCounter.machine counter) =
      ⟨some (.inr .clearInput), initialState, frame rest original counter [] []⟩ := by
  rw [MachineLogCounter.haltList_eq]
  unfold clockConfiguration
  congr 1
  funext tape
  cases tape with
  | inl i => fin_cases i <;> simp [clockTapes, frame, MachineLogCounter.configuration,
      MachineLogCounter.rawTapes]
  | inr k => cases k <;> rfl

end MaxCutGames.Foundations.Complexity.GraphCounterFinish

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineInitialHeaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual caller-program traces for non-destructive unary-prefix emission and
the two headers of the raw initial graph. Unread suffixes are never scanned.
-/

namespace MaxCutGames.Foundations.Complexity.MachineInitialHeaders

open Turing
open Reduction.MachineTransfer
open Reduction.MachineSubstitution
open MachineCopy

variable {K Λ σ : Type} [DecidableEq K]

def prefixScan (source scratch output : K) (scale : ℕ) (again restore : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push scratch (fun _ => true)
        (pushWord output (List.replicate scale true) (.goto fun _ => again)))
      (.branch (fun state => state.2.isSome)
        (.push source (fun _ => false)
          (.load (fun state => (state.1, none)) (.goto fun _ => restore)))
        (.load (fun state => (state.1, none)) (.goto fun _ => restore))))

theorem update_source_inline_MachineInitialHeaders (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      source replacement = forkTapes source scratch output base replacement saved emitted := by
  funext k
  by_cases hs : k = source
  · subst k; simp [forkTapes, hst, hso]
  · by_cases ht : k = scratch
    · subst k; simp [forkTapes, Ne.symm hst, hto]
    · by_cases ho : k = output
      · subst k; simp [forkTapes, Ne.symm hso]
      · simp [forkTapes, hs, ht, ho]

theorem update_scratch_inline_MachineInitialHeaders (source scratch output : K) (hto : scratch ≠ output)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      scratch replacement = forkTapes source scratch output base input replacement emitted := by
  funext k
  by_cases ht : k = scratch
  · subst k; simp [forkTapes, hto]
  · by_cases ho : k = output
    · subst k; simp [forkTapes, Ne.symm hto]
    · simp [forkTapes, ht, ho]

theorem update_output_inline_MachineInitialHeaders (source scratch output : K)
    (base : K → List Bool) (input saved emitted replacement : List Bool) :
    Function.update (forkTapes source scratch output base input saved emitted)
      output replacement = forkTapes source scratch output base input saved replacement := by
  simp [forkTapes]

theorem prefixStep_true (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (base : K → List Bool)
    (input saved emitted : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (prefixScan source scratch output scale again restore)
      (ambient, register) (forkTapes source scratch output base (true :: input) saved emitted) =
      ⟨some again, (ambient, some true), forkTapes source scratch output base input
        (true :: saved) (List.replicate scale true ++ emitted)⟩ := by
  simp [prefixScan, TM2.stepAux, hst, hso, hto, update_source_inline_MachineInitialHeaders, update_scratch_inline_MachineInitialHeaders,
    stepAux_pushWord, update_output_inline_MachineInitialHeaders]

theorem prefixStep_false (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ) (base : K → List Bool)
    (suffix saved emitted : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (prefixScan source scratch output scale again restore)
      (ambient, register) (forkTapes source scratch output base (false :: suffix) saved emitted) =
      ⟨some restore, (ambient, none),
        forkTapes source scratch output base (false :: suffix) saved emitted⟩ := by
  simp [prefixScan, TM2.stepAux, hst, hso, hto, update_source_inline_MachineInitialHeaders]

/-- The first loop takes one transition per unary bit and one for the delimiter. -/
theorem prefixScanTrace (source scratch output : K)
    (hst : source ≠ scratch) (hso : source ≠ output) (hto : scratch ≠ output)
    (scale : ℕ) (again restore : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atScan : program again = prefixScan source scratch output scale again restore)
    (base : K → List Bool) (n : ℕ) (suffix saved emitted : List Bool)
    (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, register),
        forkTapes source scratch output base (encodeWord n ++ suffix) saved emitted⟩) =
      some ⟨some restore, (ambient, none),
        forkTapes source scratch output base (false :: suffix)
          (List.replicate n true ++ saved) (List.replicate (scale * n) true ++ emitted)⟩ := by
  induction n generalizing saved emitted register with
  | zero =>
    simp only [Nat.zero_add, Function.iterate_one, MachineComposition.advance_some,
      encodeWord, List.replicate_zero, List.nil_append, List.singleton_append,
      Nat.mul_zero]
    change some (TM2.stepAux (program again) _ _) = _
    rw [atScan, prefixStep_false source scratch output hst hso hto]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (some (TM2.stepAux (program again) _ _)) = _
    rw [atScan]
    simp only [encodeWord, List.replicate_succ, List.cons_append]
    rw [prefixStep_true source scratch output hst hso hto]
    change (MachineComposition.advance (TM2.step program))^[n + 1]
      (some ⟨some again, (ambient, some true),
        forkTapes source scratch output base (encodeWord n ++ suffix)
          (true :: saved) (List.replicate scale true ++ emitted)⟩) = _
    rw [ih]
    have hs : List.replicate n true ++ true :: saved =
        true :: (List.replicate n true ++ saved) := by
      rw [replicate_append_cons_inline_MachineInitialHeaders, List.replicate_succ, List.cons_append]
    simp only [hs, Nat.mul_succ, List.replicate_add, List.append_assoc]

end MaxCutGames.Foundations.Complexity.MachineInitialHeaders

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-control preparation and enumeration for the powered-table
machine. The degree and radius determine a fixed multiplier `B = 2*d^t`.
Only the input vertex count varies at runtime, and it is stored on unary
tapes. The header machine consumes a cloned first input field, preserving
its unread suffix, and writes the three fields needed by the outer loop.

The row enumeration lemmas specify the canonical suffix invariant used with
`MachineCountedLoop`. They do not stand in for the caller's per-row machine
traces, which must be supplied by the actual walk and relation evaluator. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineLoop

open Turing

def initialTapes (n : Nat) (suffix : List Bool) : HeaderTape → List Bool
  | .source => encodeWord n ++ suffix
  | _ => []

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

/-- The loop consumes precisely the unary field, including its delimiter. -/
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

end MaxCutGames.Foundations.Complexity.PoweringMachineLoop

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRotor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

/-! Actual powering initialization on the common finite tape set. The first
unary input field is copied by the affine machine and consumed by the checked
header program. The original input and every unrelated tape are preserved.
No runtime graph or vertex count is captured by the finite program. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineInitialize

open Turing
open PoweringMachineLoop

abbrev Label := HeaderLabel ⊕ MachineUnaryAffineAt.Label

theorem boolAlphabet_eq_inline_PoweringMachineInitialize (max : Nat) :
    MachineEmbedding.Alphabet HeaderAlphabet (fun _ : ExtraTape max => Bool) =
      (fun _ : GlobalTape max => Bool) := by
  funext tape
  cases tape <;> rfl

theorem castTapes_embedding_inline_PoweringMachineInitialize {max : Nat} (header : HeaderTape → List Bool)
    (extra : ExtraTape max → List Bool) :
    castTapes_inline_PoweringMachineInitialize (boolAlphabet_eq_inline_PoweringMachineInitialize max) (MachineEmbedding.tapes header extra) =
      mergeTapes header extra := by
  funext tape
  rw [castTapes_apply_inline_PoweringMachineInitialize]
  cases tape <;> rfl

end MaxCutGames.Foundations.Complexity.PoweringMachineInitialize

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringRowData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual graph data consumed by the powered-row machine

The data fields are computed from the stored rotor and base relations. The
endpoint masks compare actual bounded word endpoints, in `allAddresses` order.
Their first true positions equal the already checked canonical address indices.

Reversing a row swaps the two masks and transposes each base predicate. Thus
one fixed row machine handles both directions. Its label lookup depends only
on the fixed degree and radius. The final identities describe the exact unary
input fields and the exact serialized relation emitted for a stored output row.

These are semantic producer-to-emitter identities. A machine implementation
that computes the input data from the serialized rotor is a separate frontend.
-/

namespace MaxCutGames.Foundations.PCP.PoweringRowData

open MaxCutGames.Foundations.Complexity
open Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

/-- The row machine scans the same increasing address-index order. -/
theorem firstMatch_of_first {S : Nat} (mask : Fin S → Bool) (i : Fin S)
    (hi : mask i = true) (hfirst : ∀ j : Fin S, j.val < i.val → mask j = false) :
    firstMatch mask = some i := by
  unfold firstMatch
  apply List.find?_ofFn_eq_some.mpr
  refine ⟨hi, i, rfl, ?_⟩
  intro j hj
  change ¬mask j = true
  simp [hfirst j hj]

theorem firstMatch_firstIndex {X : Type*} (p : X → Prop) [DecidablePred p]
    (xs : List X) (h : ∃ a ∈ xs, p a) :
    firstMatch (fun i : Fin xs.length => decide (p (xs.get i))) =
      some (firstIndex p xs h) := by
  apply firstMatch_of_first
  · exact decide_eq_true (firstIndex_matches p xs h)
  · intro j hj
    exact decide_eq_false (firstIndex_is_first p xs h j hj)

/-! ## Exact field and emitted-relation serialization -/

end MaxCutGames.Foundations.PCP.PoweringRowData

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringRowHeaderSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact tail and reverse-index fields of the actual powering-table rows.
The reverse address is affine in the live starting vertex; the coefficient
and offset depend only on the fixed degree, word, and orientation. -/

namespace MaxCutGames.Foundations.PCP.PoweringRowHeaderSemantics

open PoweringWalks PoweringEnumeration
open MaxCutGames.Foundations.Complexity

variable {vertices d : Nat}

def reverseOffset (d n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  2 * (wordEquiv d (n + 1) ports).val + (if direction then 0 else 1)

def reverseValue (d n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) : Nat :=
  blockSize d n * vertex.val + reverseOffset d n ports direction

end MaxCutGames.Foundations.PCP.PoweringRowHeaderSemantics

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variable-size vertex enumeration. The finite guard decrements the
live unary counter, a one-step bridge enters the fixed vertex producer, and the
producer returns to the guard. Work tapes may change after every vertex. -/

/-!
# Physical output headers followed by complete work-tape cleanup

The finite program first copies the dart-count word onto the existing row
output, then copies the vertex-count word, and finally drains every tape except
the output. Both unary header values are read from physical tapes; they do not
parameterize the program. Header sources and their unread suffixes are restored
by the two copies before cleanup. The final configuration contains the full
encoded header and rows on the output tape and empty words on every other tape.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

abbrev Label (enumeration : Fin N ≃ K) (output : K) :=
  MachineUnaryAffineAt.Label ⊕ (MachineUnaryAffineAt.Label ⊕
    MachineDrainMany.Label (MachineDrainMany.workTapes enumeration output))

end MaxCutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringRuntimeBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finishing cost from the actual preceding machine execution

Every stack can grow by at most the fixed program's push bound in one
transition. Consequently an actual bounded execution from the standard input
configuration supplies the uniform stack bound needed by the finishing phase.
The bound below uses the same global machine for that preceding execution; no
separate tape-size hypothesis or numerical simulation is substituted for it.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringRuntimeBudget

open Turing

/-- Uniform stack growth along an actual execution, from any initial configuration. -/
theorem stackLength_le_of_execution (tm : FinTM2) (start finish : tm.Cfg)
    (initialBound priorBudget : Nat)
    (initial : ∀ k, (start.stk k).length ≤ initialBound)
    (prior : StateTransition.EvalsToInTime tm.step start (some finish) priorBudget)
    (k : tm.K) :
    (finish.stk k).length ≤ initialBound + priorBudget * Runtime.programPushBound tm := by
  have grown := Runtime.executionSizeBound tm.step (fun cfg => (cfg.stk k).length)
    (Runtime.programPushBound tm) (Runtime.stepStackLength tm k) prior
  exact grown.trans (Nat.add_le_add_right (initial k) _)

/-- Standard input initialization bounds every initial stack by the input length. -/
theorem stackLength_le_from_input (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (finish : tm.Cfg) (priorBudget : Nat)
    (prior : StateTransition.EvalsToInTime tm.step (initList tm input)
      (some finish) priorBudget) (k : tm.K) :
    (finish.stk k).length ≤ input.length + priorBudget * Runtime.programPushBound tm :=
  stackLength_le_of_execution tm (initList tm input) finish input.length priorBudget
    (Runtime.initialStackLength tm input) prior k

end MaxCutGames.Foundations.Complexity.PoweringRuntimeBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

namespace MaxCutGames.Foundations.PCP.FinalConstants

def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2

end MaxCutGames.Foundations.PCP.FinalConstants

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace MaxCutGames.Foundations.PCP.RoundTables

/-- Initialized fixed data keep enormous constant powers symbolic in the kernel.
The stored equality proves the exact requested parameter; no value is assumed. -/
opaque fixedWalkParameter : {n : Nat // n = 2 * FinalConstants.endpointLength} :=
  ⟨2 * FinalConstants.endpointLength, rfl⟩

def walkParameter : Nat := fixedWalkParameter.val

theorem degree_positive : 0 < PreprocessingTables.degree := by
  unfold PreprocessingTables.degree
  omega

end MaxCutGames.Foundations.PCP.RoundTables

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

def copySource : CopyPhase → Tape
  | .tailVariables _ | .dummyVariables => .«variables»
  | .variableName slot => .field (nameField slot)
  | _ => .index

def finalTape (slot : Fin 3) : Tape :=
  if slot.val = 0 then .«variables» else if slot.val = 1 then .counter else .index

def headerTape (slot : Fin 2) : Tape := if slot.val = 0 then .«variables» else .counter

end MaxCutGames.Foundations.PCP.RawInitialMachineModel

/-!
Actual execution of the raw initial graph machine from its standard input
configuration to the first clause-loop guard. The unread clause bits are
preserved verbatim, and all tape contents at the boundary are explicit.
-/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

def inputTapes (bits : List Bool) : Tape → List Bool
  | .input => bits
  | _ => []

end MaxCutGames.Foundations.PCP.RawInitialMachineStart

/-! The exact input and output streams at successive clause-loop iterations.
These tape invariants use the actual word codecs and clause occurrence order. -/

/-! Actual execution of the raw initial graph program's reusable phases. -/

/-!
Read exactly one concrete six-field CNF clause in the actual global machine,
then execute its real sign-loading instruction. No extra finish transition
is inserted. Every unrelated tape and the unread input suffix are preserved.
-/

/-! The six incidence rows are emitted by the actual finite program, with
their exact order, full relation lists, transition count, and tape frame. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineCleanup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual cleanup of all six clause-field tapes followed by the global unary
index increment. The output accumulator, unread input, and other caller tapes
are preserved, and no additional finish instruction is assumed.
-/

/-! One complete clause iteration of the actual initial graph machine. -/

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

/-! Exact execution of the clause loop, in the original occurrence order. -/

/-! The actual finite machine computing the initial graph's full serialized
table. The runtime bound counts every parse, row, cleanup and output reversal. -/

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

namespace Program

open PCP.AlphabetTable

inductive Label (headerCount rowCount : Nat)
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts | seedIndex
  | header (label : Emitter.Label headerCount 36864)
  | headerClearTail | headerClearHead
  | guard | startTail | readTail | startReverse | readReverse
  | headTableFirst | headTableSecond | headIndexFirst | headIndexSecond
  | headHeaderVertices | headHeaderDarts | headLookup (label : Lookup.Label)
  | readRelation
  | row (label : Emitter.Label rowCount 36864)
  | clearTail | clearHead | clearReverse | nextRow | reverseOutput
  deriving DecidableEq, Fintype

end Program

end MaxCutGames.Foundations.Complexity.FinalCNFMachine

end OAI
end


