-- Prove2me | Definitions.Def_OAIQ087A003
-- name    : OAIQ087A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:16:53.710742+00:00
-- url     : https://prove2.me/theorems/746e0191-08f9-423b-aa9d-51ea3921d971
-- title:
--   Definitions bundle OAIQ087A003 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 833 declarations of OpenAI's Lean: 439 definitions, 48 inductive types or structures, 23 instances and 323 theorems. The definitions and types are `OAI.MaxCutGames.Explicit.MachineClone100Certified.timePolynomial`, `OAI.MaxCutGames.Explicit.MachineClone100Loop.Record`, `OAI.MaxCutGames.Explicit.MachineClone100Loop.recordWords`, `OAI.MaxCutGames.Explicit.MachineClone100Model.Alphabet`, `OAI.MaxCutGames.Explicit.MachineClone100Model.Context`, `OAI.MaxCutGames.Explicit.MachineClone100Model.Label`, `OAI.MaxCutGames.Explicit.MachineClone100Model.State`, `OAI.MaxCutGames.Explicit.MachineClone100Model.Tape`, `OAI.MaxCutGames.Explicit.MachineClone100Model.cleanupNext`, `OAI.MaxCutGames.Explicit.MachineClone100Model.contextNext`, `OAI.MaxCutGames.Explicit.MachineClone100Model.contextOffset`, `OAI.MaxCutGames.Explicit.MachineClone100Model.contextScale`, `OAI.MaxCutGames.Explicit.MachineClone100Model.contextSource`, `OAI.MaxCutGames.Explicit.MachineClone100Model.defaultControl`, `OAI.MaxCutGames.Explicit.MachineClone100Model.drain`, `OAI.MaxCutGames.Explicit.MachineClone100Model.headerTape`, `OAI.MaxCutGames.Explicit.MachineClone100Model.initialState`, `OAI.MaxCutGames.Explicit.MachineClone100Model.tripleField`, `OAI.MaxCutGames.Explicit.MachineClone100Triples.affineRecord`, `OAI.MaxCutGames.Explicit.MachineProductField.Layout`, `OAI.MaxCutGames.Explicit.MachineProductField.Ready`, `OAI.MaxCutGames.Explicit.MachineProductField.clearTapes`, `OAI.MaxCutGames.Explicit.MachineProductField.gatherSlots`, `OAI.MaxCutGames.Explicit.MachineProductGather.Tape`, `OAI.MaxCutGames.Explicit.MachineProductGather.lookupRole`, `OAI.MaxCutGames.Explicit.MachineProductGather.shift`, `OAI.MaxCutGames.Explicit.MachineProductPower.digits`, `OAI.MaxCutGames.Explicit.MachineProductProgram.Extra`, `OAI.MaxCutGames.Explicit.MachineProductRow.Command`, `OAI.MaxCutGames.Explicit.MachineProductRow.Layout`, `OAI.MaxCutGames.Explicit.MachineProductRow.fieldRole`, `OAI.MaxCutGames.Explicit.MachineProductRow.fieldSlots`, `OAI.MaxCutGames.Explicit.MachineProductRow.outputTape`, `OAI.MaxCutGames.Explicit.MachineProductSeed.Command`, `OAI.MaxCutGames.Explicit.MachineProductSeed.LocalLabel`, `OAI.MaxCutGames.Explicit.MachineProductSeed.result`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitProgram.State`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitProgram.initialState`, `OAI.MaxCutGames.Explicit.MachineSingleOrbitRuntime.prefixPolynomial`, `OAI.MaxCutGames.Explicit.MachineSubdivisionBody.incrementTapes` and 447 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_InputData`, `MaxCut_Estimates_Basic`, `MaxCut_Games_AddressOdometerSchedule`, `MaxCut_Games_Basic2`, `MaxCut_Games_Clone100Counting`, `MaxCut_Games_EquationLookup`, `MaxCut_Games_FinalCNFHeader`, `MaxCut_Games_FinalCNFOutput`, `MaxCut_Games_FinalCNFStream`, `MaxCut_Games_FinishBounds`, `MaxCut_Games_LabelBound`, `MaxCut_Games_OccurrenceTupleOrder`, `MaxCut_Games_Product`, `MaxCut_Games_ProductTarget`, `MaxCut_Games_Subdivision`, `MaxCut_Machines_Alphabet`, `MaxCut_Machines_CloneMachineModel`, `MaxCut_Machines_CompareLoop`, `MaxCut_Machines_GraphCounterFinish`, `MaxCut_Machines_Input`, `MaxCut_Machines_Lookup`, `MaxCut_Machines_Machine`, `MaxCut_Machines_MachineCanonicalOutput`, `MaxCut_Machines_MachineClone100`, `MaxCut_Machines_MachineClone100Table`, `MaxCut_Machines_MachineClone100Triples`, `MaxCut_Machines_MachineCloudCount`, `MaxCut_Machines_MachineCloudPadding`, `MaxCut_Machines_MachineCloudPrefix`, `MaxCut_Machines_MachineCloudSelect`, `MaxCut_Machines_MachineDummyRows`, `MaxCut_Machines_MachineExpanderFamilyAffine`, `MaxCut_Machines_MachineExpanderFamilyCycle`, `MaxCut_Machines_MachineExpanderRowFrames`, `MaxCut_Machines_MachineExpanderTableRows`, `MaxCut_Machines_MachineFieldProfile`, `MaxCut_Machines_MachineFieldTemplate`, `MaxCut_Machines_MachineHorner`, `MaxCut_Machines_MachineInitialHeaders`, `MaxCut_Machines_MachineLazyRows`, `MaxCut_Machines_MachineLazyTable`, `MaxCut_Machines_MachineLazyTableRuntime`, `MaxCut_Machines_MachineLookupCore`, `MaxCut_Machines_MachineOverlayRows`, `MaxCut_Machines_MachineOverlayTable`, `MaxCut_Machines_MachinePaddedExpanderFamilyBounds`, `MaxCut_Machines_MachinePortReindex`, `MaxCut_Machines_MachineProductGatherBounds`, `MaxCut_Machines_MachineProductProgram`, `MaxCut_Machines_MachineRegisterEmit`, `MaxCut_Machines_MachineRegularLift`, `MaxCut_Machines_MachineRegularMetadata`, `MaxCut_Machines_MachineRegularOriginalBody`, `MaxCut_Machines_MachineRegularOwnerProgram`, `MaxCut_Machines_MachineRegularTableRuntime`, `MaxCut_Machines_MachineRegularTableTrace`, `MaxCut_Machines_MachineRegularVertexBlock`, `MaxCut_Machines_MachineRhsLoad`, `MaxCut_Machines_MachineSequential`, `MaxCut_Machines_MachineSingleOrbitProgram`, `MaxCut_Machines_MachineSubdivisionCorrespondence`, `MaxCut_Machines_MachineSubdivisionDynamicRows`, `MaxCut_Machines_MachineSubdivisionRows`, `MaxCut_Machines_MachineSubdivisionTableRead`, `MaxCut_Machines_MachineSubroutine`, `MaxCut_Machines_MachineTemplateAddress`, `MaxCut_Machines_MachineTupleOdometer`, `MaxCut_Machines_MachineUnaryAffine`, `MaxCut_Machines_MachineUnaryMultiply`, `MaxCut_Machines_RawInitialMachineCleanup`, `MaxCut_Machines_RawInitialMachineModel`, `MaxCut_Machines_Relations`, `MaxCut_Machines_Runtime2`, `MaxCut_Machines_RuntimeModel`, `MaxCut_Machines_RuntimeSpace`, `MaxCut_Machines_SelectorMachine`, `MaxCut_Model2`, `MaxCut_PCP_AnalyticCheeger`, `MaxCut_PCP_Folding`, `MaxCut_PCP_GraphTableComplexity`, `MaxCut_PCP_KernelIteration`, `MaxCut_PCP_LoopOrder`, `MaxCut_PCP_Overlap`, `MaxCut_PCP_Parameters`, `MaxCut_PCP_PreprocessingLazyWords`, `MaxCut_PCP_PreprocessingOverlayWords`, `MaxCut_PCP_PreprocessingPaddingOffsets`, `MaxCut_PCP_PreprocessingRegularLoopWords`, `MaxCut_PCP_ProductCollisionBounds`, `MaxCut_PCP_RawInitialPredicate`, `MaxCut_PCP_RawInitialTables`, `MaxCut_PCP_RoundGap`, `MaxCut_PCP_Rounding`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A009`, `OAIQ087A010`, `OAIQ087A011` and `OAIQ087A012`; the statement `OAI_MaxCutGames_Decoder_MatrixGap_parameters_of_inverse`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ087_MC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

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

namespace MaxCutGames.Reduction.MachineTransducer

open Turing

def tapeStacks (input output : List Bool) : Bool → List Bool :=
  fun side => if side then output else input

theorem update_input_inline_MachineTransducer (input output replacement : List Bool) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> simp [tapeStacks]

theorem update_output_inline_MachineTransducer (input output replacement : List Bool) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> simp [tapeStacks]

variable {Q : Type} [Fintype Q]

/-- The semantic output, with the control state updated after each input bit. -/
def output (transition : Q → Bool → Q) (emit : Q → Bool → List Bool) :
    Q → List Bool → List Bool
  | _, [] => []
  | state, symbol :: input =>
      emit state symbol ++ output transition emit (transition state symbol) input

def loop (initial : Q) :
    TM2.Stmt (fun _ : Bool => Bool) (Option (Q × Bool)) (Q × Option Bool) :=
  .pop false (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun state => some (state.1, state.2.getD false))
      (.load (fun _ => (initial, none)) .halt))

end MaxCutGames.Reduction.MachineTransducer

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Machine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceMachine

open Turing

variable {K Λ σ : Type} [DecidableEq K]

def fieldTapes (source destination : K) (base : K → List Bool)
    (input output : List Bool) : K → List Bool :=
  Function.update (Function.update base source input) destination output

@[simp] theorem fieldTapes_source (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output source = input := by
  simp [fieldTapes, hne]

@[simp] theorem fieldTapes_destination (source destination : K)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output destination = output := by
  simp [fieldTapes]

@[simp] theorem fieldTapes_self (source destination : K) (base : K → List Bool) :
    fieldTapes source destination base (base source) (base destination) = base := by
  simp [fieldTapes]

theorem fieldTapes_other (source destination p : K)
    (hpS : p ≠ source) (hpD : p ≠ destination)
    (base : K → List Bool) (input output : List Bool) :
    fieldTapes source destination base input output p = base p := by
  simp [fieldTapes, hpS, hpD]

theorem update_field_source_inline_SourceMachine (source destination : K) (hne : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) source replacement =
      fieldTapes source destination base replacement output := by
  funext p
  by_cases hs : p = source
  · subst p; simp [fieldTapes, hne]
  · by_cases hd : p = destination
    · subst p; simp [fieldTapes, Ne.symm hne]
    · simp [fieldTapes, hs, hd]

theorem update_field_destination_inline_SourceMachine (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (fieldTapes source destination base input output) destination replacement =
      fieldTapes source destination base input replacement := by
  simp [fieldTapes]

def fieldNext (start : Fin 4 → Λ) (exit : Option Λ) (j : Fin 4) : Option Λ :=
  match j.val with
  | 0 => some (start 1)
  | 1 => some (start 2)
  | 2 => some (start 3)
  | _ => exit

end MaxCutGames.Foundations.Hastad.SourceMachine

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

open Turing

variable {K Λ σ : Type} [DecidableEq K]

/-- An executable complete cleanup list from an explicit finite enumeration. -/
def workTapes {N : Nat} (enumeration : Fin N ≃ K) (output : K) : List K :=
  (List.ofFn (fun i => enumeration i)).filter (fun k => decide (k ≠ output))

@[simp] theorem mem_workTapes {N : Nat} (enumeration : Fin N ≃ K) (output k : K) :
    k ∈ workTapes enumeration output ↔ k ≠ output := by
  have hmem : k ∈ List.ofFn (fun i => enumeration i) := by
    apply List.mem_ofFn.mpr
    exact ⟨enumeration.symm k, enumeration.apply_symm_apply k⟩
  simp [workTapes, hmem]

theorem workTapes_length_le {N : Nat} (enumeration : Fin N ≃ K) (output : K) :
    (workTapes enumeration output).length ≤ N := by
  simpa only [workTapes, List.length_ofFn] using
    List.length_filter_le (fun k => decide (k ≠ output)) (List.ofFn (fun i => enumeration i))

end MaxCutGames.Foundations.Complexity.MachineDrainMany

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineFieldTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.MachineFieldTemplate

open Turing
open MaxCutGames.Foundations.Complexity

variable {q : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem chain_inline_MachineFieldTemplate {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

end MaxCutGames.Reduction.MachineFieldTemplate

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineUnaryAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineUnaryAffineAt

open Turing

variable {K Λ σ : Type} [DecidableEq K]

inductive Label
  | seed | scan | restore
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.seed, .scan, .restore]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

end MaxCutGames.Foundations.Complexity.MachineUnaryAffineAt

/-! A real finite program for uniform whole-instance copying. It reads three
headers, physically multiplies the occurrence count by the fixed constant,
copies the header-free body the same fixed number of times, and clears all
working tapes. No input-dependent data are placed in finite control. -/

namespace MaxCutGames.Explicit.MachineUniformProgram

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad

inductive Tape
  | input | vertices | alphabet | occurrences | newOccurrences
  | affineScratch | copyScratch | accumulator | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .vertices, .alphabet, .occurrences,
  .newOccurrences, .affineScratch, .copyScratch, .accumulator, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def headerField : Fin 3 → Tape
  | 0 => .vertices
  | 1 => .alphabet
  | 2 => .occurrences

def emitField : Fin 4 → Tape
  | 0 => .vertices
  | 1 => .alphabet
  | 2 => .newOccurrences
  | 3 => .input

def clearKeys : List Tape :=
  [.input, .vertices, .alphabet, .occurrences, .newOccurrences,
    .affineScratch, .copyScratch]

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  cases k <;> simp_all [clearKeys]

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

end MaxCutGames.Explicit.MachineUniformProgram

/-! Exact execution of the three input-header reads of uniform copying. -/

namespace MaxCutGames.Explicit.MachineUniformHeaders

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineUniformProgram

def inputTapes (bits : List Bool) : Tape → List Bool :=
  fun k => if k = .input then bits else []

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

namespace MaxCutGames.Foundations.Hastad.SourceRuntimeSpace

open Turing Complexity
open scoped BigOperators

attribute [local instance] FinTM2.kFin

/-- All stacks are counted, even when their symbol types differ. -/
def configurationLength (tm : FinTM2) (cfg : tm.Cfg) : Nat :=
  ∑ k : tm.K, (cfg.stk k).length

theorem initial_configurationLength (tm : FinTM2) (input : List (tm.Γ tm.k₀)) :
    configurationLength tm (initList tm input) = input.length := by
  have point (k : tm.K) : ((initList tm input).stk k).length =
      if k = tm.k₀ then input.length else 0 := by
    by_cases h : k = tm.k₀
    · subst k
      simp [initList]
    · simp [initList, h]
  simp [configurationLength, point]

end MaxCutGames.Foundations.Hastad.SourceRuntimeSpace

/-! A fixed finite TM2 interpreter for a unary number of runs of a fixed
certified machine. The counter is data on a separate tape. Every body run is
lifted from an actual `TM2OutputsInTime` witness, and all transfers are executed
by the checked finite transfer loops. -/

namespace MaxCutGames.Foundations.Complexity.MachineRepeat
open Turing

inductive ExtraTape | counter | temporary | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.counter, .temporary, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide
inductive Phase | parse | guard | bodyToTemp | tempToBody | finalToTemp | tempToOutput
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.parse, .guard, .bodyToTemp, .tempToBody,
  .finalToTemp, .tempToOutput]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape (M : FinTM2) := M.K ⊕ ExtraTape
abbrev Label (M : FinTM2) := M.Λ ⊕ Phase
abbrev State (M : FinTM2) := M.σ × Option (M.Γ M.k₀)

def extraTapes (M : FinTM2) (counter temporary output : List (M.Γ M.k₀)) :
    ExtraTape → List (M.Γ M.k₀)
  | .counter => counter
  | .temporary => temporary
  | .output => output

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
open MaxCutGames.Foundations
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MachineUniformProgram

noncomputable def prefixPolynomial (C : Nat) : Polynomial Nat :=
  Polynomial.C (3 * C + 6) * Polynomial.X + Polynomial.C (3 * C + 16)

end MaxCutGames.Explicit.MachineUniformRun

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.MachineSubdivisionRows

open Turing
open MaxCutGames.Foundations
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction

/-- The semantic subdivision numbering: originals and middle vertices on the
left, then two private right vertices for each occurrence. -/
def subdivisionVertexWords (n Q u v e : Nat) : Fin 5 → Nat
  | 0 => u
  | 1 => n + Q + 2 * e
  | 2 => n + e
  | 3 => n + Q + 2 * e + 1
  | 4 => v

end MaxCutGames.Explicit.MachineSubdivisionRows

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

namespace MaxCutGames.Explicit.MachineSubdivisionProgram

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction

inductive Tape
  | input | vertices | alphabetHeader | occurrences | remaining
  | newVertices | newEdges | u | v | middle | first | last
  | permutation | permutationReverse | affineScratch | copyScratch
  | accumulator | output
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .vertices, .alphabetHeader, .occurrences,
  .remaining, .newVertices, .newEdges, .u, .v, .middle, .first, .last, .permutation,
  .permutationReverse, .affineScratch, .copyScratch, .accumulator, .output]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def headerField : Fin 3 → Tape
  | 0 => .vertices
  | 1 => .alphabetHeader
  | 2 => .occurrences

def rowField : Fin 6 → Tape
  | 0 => .u
  | 1 => .first
  | 2 => .middle
  | 3 => .last
  | 4 => .v
  | 5 => .permutation

def newHeaderField : Fin 2 → Tape
  | 0 => .newVertices
  | 1 => .newEdges

/-- Nine fixed affine passes initialize_ headers, the loop counter, and all three
private vertex indices. `none` means accumulate into the existing unary word. -/
structure InitOp where
  source : Tape
  destination : Tape
  coefficient : Nat
  seed : Option Nat

def initOp : Fin 9 → InitOp
  | 0 => ⟨.vertices, .newVertices, 1, some 0⟩
  | 1 => ⟨.occurrences, .newVertices, 3, none⟩
  | 2 => ⟨.occurrences, .newEdges, 4, some 0⟩
  | 3 => ⟨.vertices, .middle, 1, some 0⟩
  | 4 => ⟨.vertices, .first, 1, some 0⟩
  | 5 => ⟨.occurrences, .first, 1, none⟩
  | 6 => ⟨.vertices, .last, 1, some 1⟩
  | 7 => ⟨.occurrences, .last, 1, none⟩
  | 8 => ⟨.occurrences, .remaining, 1, some 0⟩

def clearKeys : List Tape :=
  [.input, .vertices, .alphabetHeader, .occurrences, .remaining,
   .newVertices, .newEdges, .u, .v, .middle, .first, .last,
   .permutation, .permutationReverse, .affineScratch, .copyScratch]

theorem accumulator_not_mem_clearKeys : Tape.accumulator ∉ clearKeys := by decide
theorem output_not_mem_clearKeys : Tape.output ∉ clearKeys := by decide

end MaxCutGames.Explicit.MachineSubdivisionProgram

/-! Exact execution of the three input-header reads of subdivision. -/

namespace MaxCutGames.Explicit.MachineSubdivisionHeaders

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineSubdivisionProgram

def inputTapes (bits : List Bool) : Tape → List Bool :=
  fun k => if k = .input then bits else []

end MaxCutGames.Explicit.MachineSubdivisionHeaders

/-! Physical header arithmetic and private-vertex initialization. -/

namespace MaxCutGames.Explicit.MachineSubdivisionInit

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def sourceValue (n Q : Nat) : Fin 9 → Nat
  | 0 => n
  | 1 => Q
  | 2 => Q
  | 3 => n
  | 4 => n
  | 5 => Q
  | 6 => n
  | 7 => Q
  | 8 => Q

def beforeValue (n : Nat) : Fin 9 → Nat
  | 0 => 0
  | 1 => n
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => n
  | 6 => 0
  | 7 => n + 1
  | 8 => 0

def afterValue (n Q : Nat) (i : Fin 9) : Nat :=
  (initOp i).coefficient * sourceValue n Q i + (initOp i).seed.getD (beforeValue n i)

def stageCost (n Q : Nat) : Nat := 2 * (n + Q + 1) + 1

end MaxCutGames.Explicit.MachineSubdivisionInit

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

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/
namespace MaxCutGames.Foundations.Complexity.MachineLookupSpec

/-! Bounds on the proposed lookup recurrence. A separate machine proof must
identify these counts with actual transition traces. -/

def steps : List Nat → Nat → Nat
  | [], i => 2 * i + 2
  | n :: _, 0 => n + 3
  | n :: ns, i + 1 => n + 2 + steps ns i

end MaxCutGames.Foundations.Complexity.MachineLookupSpec

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
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Folding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit half-table storage, odd folding, and conditioning on the finite
set of satisfying local assignments for Håstad's test. -/

namespace MaxCutGames.Reduction.CloneGap

variable {α β : Type*}

abbrev Index := Nat

end MaxCutGames.Reduction.CloneGap

/-!
Actual equations for clause contexts having no valid local assignment. The
right answer is the constant false bit, represented by two occurrences of one
dummy variable. Those occurrences cancel for every assignment. The remaining
left answer is folded, so its uniform bias is exactly zero.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Basic2
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

section

/-- Return the first proposal accepted by the given test, or report exhaustion. -/
def firstAccepted {σ : Type*} (accept : σ → Bool) : List σ → Option σ
  | [] => none
  | proposal :: rest =>
      if accept proposal then some proposal else firstAccepted accept rest

/-- If the first proposal accepted by either sampler is accepted by both,
the two samplers return exactly that same proposal. -/
theorem first_union_common {σ : Type*} (left right : σ → Bool)
    (proposals : List σ) (proposal : σ)
    (hfirst : firstAccepted (fun s => left s || right s) proposals = some proposal)
    (hleft : left proposal = true) (hright : right proposal = true) :
    firstAccepted left proposals = some proposal ∧
      firstAccepted right proposals = some proposal := by
  induction proposals with
  | nil => simp [firstAccepted] at hfirst
  | cons head tail ih =>
      by_cases hl : left head = true
      · have heq : head = proposal := by
          simpa [firstAccepted, hl] using hfirst
        subst head
        simp [firstAccepted, hleft, hright]
      · by_cases hr : right head = true
        · have heq : head = proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          subst head
          exact False.elim (hl hleft)
        · have htail : firstAccepted (fun s => left s || right s) tail = some proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          simpa [firstAccepted, hl, hr] using ih htail

end

/-!
Exact finite probability mass of a bounded rejection process.

Each trial independently draws from a finite mass function `w`. Its first
accepted proposal is represented by `some proposal`; exhaustion is `none`.
The recursive definition exposes the one-step probability transition. We prove
normalization, nonnegativity, the exact survival probability, and an exact
agreement-event formula with the finite-truncation error.
-/

section

variable {σ : Type*} [Fintype σ]

def eventMass (w : σ → ℝ) (event : σ → Bool) : ℝ :=
  ∑ s, if event s then w s else 0

theorem eventMass_nonneg (w : σ → ℝ) (event : σ → Bool) (hw : ∀ s, 0 ≤ w s) :
    0 ≤ eventMass w event := by
  apply Finset.sum_nonneg
  intro s _
  split <;> simp_all

theorem eventMass_complement (w : σ → ℝ) (event : σ → Bool)
    (hw : ∑ s, w s = 1) :
    eventMass w event + eventMass w (fun s => !(event s)) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ s, ((if event s then w s else 0) + (if !event s then w s else 0)) = ∑ s, w s := by
      apply Finset.sum_congr rfl
      intro s _
      cases event s <;> simp
    _ = 1 := hw

def geometricMass (r : ℝ) : Nat → ℝ
  | 0 => 0
  | n + 1 => 1 + r * geometricMass r n

theorem geometricMass_identity (r : ℝ) (n : Nat) :
    (1 - r) * geometricMass r n = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih =>
      simp only [geometricMass, pow_succ]
      calc
        (1 - r) * (1 + r * geometricMass r n) =
            (1 - r) + r * ((1 - r) * geometricMass r n) := by ring
        _ = 1 - r ^ n * r := by rw [ih]; ring

/-- Probability transition for a finite first-acceptance process. A successful
first trial contributes its own mass; a rejected first trial continues with
one fewer trial. -/
def firstHitWeight (w : σ → ℝ) (accept : σ → Bool) : Nat → Option σ → ℝ
  | 0, none => 1
  | 0, some _ => 0
  | n + 1, none => eventMass w (fun s => !(accept s)) * firstHitWeight w accept n none
  | n + 1, some s =>
      (if accept s then w s else 0) +
        eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some s)

theorem firstHitWeight_some (w : σ → ℝ) (accept : σ → Bool) (n : Nat) (s : σ) :
    firstHitWeight w accept n (some s) =
      (if accept s then w s else 0) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  induction n with
  | zero => simp [firstHitWeight, geometricMass]
  | succ n ih =>
      rw [firstHitWeight, geometricMass, ih]
      ring

/-- Probability that the first accepted proposal satisfies an additional test.
For two threshold samplers, take `accept = left || right` and `good = left && right`.
`first_union_common` gives deterministic agreement on this event. -/
def goodFirstMass (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) : ℝ :=
  ∑ s, if good s then firstHitWeight w accept n (some s) else 0

theorem goodFirstMass_eq (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  unfold goodFirstMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstHitWeight_some]
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, eventMass]

/-- Exact finite geometric law: the first accepted proposal lies in the good
part with probability (good accepted mass / total accepted mass) times the
probability of seeing any accepted proposal within the trial bound. -/
theorem goodFirstMass_exact (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (ha : eventMass w accept ≠ 0) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) / eventMass w accept *
        (1 - eventMass w (fun s => !(accept s)) ^ n) := by
  rw [goodFirstMass_eq]
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have hgeom : eventMass w accept *
      geometricMass (eventMass w (fun s => !(accept s))) n =
      1 - eventMass w (fun s => !(accept s)) ^ n := by
    have heq : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
    rw [heq, hg]
  rw [← hgeom]
  field_simp

theorem commonMass_le_acceptMass (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) :
    eventMass w (fun s => accept s && good s) ≤ eventMass w accept := by
  apply Finset.sum_le_sum
  intro s _
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, hw s]

/-- A finite truncation loses at most its exhaustion probability in addition
to the conditional bad-first-proposal probability. All quantities are exact
finite sums; the rightmost term is the explicit geometric tail. -/
theorem goodFirstMass_lower_bound (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∀ s, 0 ≤ w s) (hw_sum : ∑ s, w s = 1)
    (ha : 0 < eventMass w accept) (n : Nat) :
    eventMass w (fun s => accept s && good s) / eventMass w accept -
        eventMass w (fun s => !(accept s)) ^ n ≤ goodFirstMass w accept good n := by
  rw [goodFirstMass_exact w accept good hw_sum (ne_of_gt ha) n]
  have hratio : eventMass w (fun s => accept s && good s) / eventMass w accept ≤ 1 := by
    apply (div_le_one ha).2
    exact commonMass_le_acceptMass w accept good hw
  have htail : 0 ≤ eventMass w (fun s => !(accept s)) ^ n :=
    pow_nonneg (eventMass_nonneg w (fun s => !(accept s)) hw) n
  nlinarith

/-!
Connect the rejection sampler's executable list recursion to exact finite
probabilities. `traceAverage` is a finite nested sum over independent proposals;
it introduces no assumed probability law. The main theorem computes the actual
mass of each output of `firstAccepted` under those nested sums.
-/

/-- Expectation over a length-n list of independent proposals with mass `w`.
This is defined directly as a finite nested weighted sum. -/
def traceAverage (w : σ → ℝ) : Nat → (List σ → ℝ) → ℝ
  | 0, observable => observable []
  | n + 1, observable => ∑ s, w s * traceAverage w n (fun tail => observable (s :: tail))

theorem traceAverage_const (w : σ → ℝ) (hw : ∑ s, w s = 1) (n : Nat) (c : ℝ) :
    traceAverage w n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [traceAverage, ih, ← Finset.sum_mul, hw]

theorem traceAverage_mono (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (n : Nat)
    (f g : List σ → ℝ) (hfg : ∀ xs, f xs ≤ g xs) :
    traceAverage w n f ≤ traceAverage w n g := by
  induction n generalizing f g with
  | zero => exact hfg []
  | succ n ih =>
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (ih (fun tail => f (s :: tail)) (fun tail => g (s :: tail))
          (fun tail => hfg (s :: tail))) (hw s)

theorem traceAverage_sum {ι : Type*} [Fintype ι] (w : σ → ℝ) (n : Nat)
    (f : ι → List σ → ℝ) :
    traceAverage w n (fun xs => ∑ i, f i xs) = ∑ i, traceAverage w n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [traceAverage]
      simp_rw [ih, Finset.mul_sum]
      exact Finset.sum_comm

variable [DecidableEq σ]

/-- The recursively constructed first-hit distribution is the actual law
of the finite shared-list rejection sampler. -/
theorem firstAccepted_law (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) (output : Option σ) :
    traceAverage w n (fun proposals =>
      if firstAccepted accept proposals = output then 1 else 0) =
      firstHitWeight w accept n output := by
  classical
  induction n generalizing output with
  | zero => cases output <;> simp [traceAverage, firstAccepted, firstHitWeight]
  | succ n ih =>
      have hstep : traceAverage w (n + 1) (fun proposals =>
          if firstAccepted accept proposals = output then 1 else 0) =
          ∑ s, w s * (if accept s then (if some s = output then 1 else 0)
            else firstHitWeight w accept n output) := by
        unfold traceAverage
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        by_cases hs : accept s = true
        · simp [firstAccepted, hs, traceAverage_const w hw]
        · simpa [firstAccepted, hs] using ih output
      rw [hstep]
      cases output with
      | none =>
          simp only [Option.some_ne_none, ite_false, firstHitWeight]
          rw [eventMass, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          cases accept s <;> simp
      | some t =>
          simp only [Option.some.injEq, firstHitWeight]
          calc
            ∑ s, w s * (if accept s then (if s = t then 1 else 0)
                else firstHitWeight w accept n (some t)) =
              ∑ s, ((if s = t then (if accept s then w s else 0) else 0) +
                (if !(accept s) then w s else 0) * firstHitWeight w accept n (some t)) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  by_cases he : s = t
                  · subst s
                    by_cases hs : accept t = true <;> simp [hs]
                  · by_cases hs : accept s = true <;> simp [hs, he]
            _ = (if accept t then w t else 0) +
                eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some t) := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
                  simp [eventMass]

/-- Indicator of the first accepted proposal passing a second test. -/
def goodFirstIndicator (accept good : σ → Bool) (proposals : List σ) : ℝ :=
  match firstAccepted accept proposals with
  | none => 0
  | some s => if good s then 1 else 0

theorem goodFirstIndicator_expansion (accept good : σ → Bool) (proposals : List σ) :
    goodFirstIndicator accept good proposals =
      ∑ s, if good s then (if firstAccepted accept proposals = some s then 1 else 0) else 0 := by
  classical
  cases h : firstAccepted accept proposals with
  | none => simp [goodFirstIndicator, h]
  | some t =>
      simp only [goodFirstIndicator, h, Option.some.injEq]
      calc
        (if good t then (1 : ℝ) else 0) =
            ∑ s, if t = s then (if good s then (1 : ℝ) else 0) else 0 := by simp
        _ = ∑ s, if good s then (if t = s then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hg : good s = true <;> by_cases ht : t = s <;> simp [hg, ht]

/-- Exact good-event probability of the actual bounded sampler. -/
theorem goodFirstIndicator_law (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) :
    traceAverage w n (goodFirstIndicator accept good) = goodFirstMass w accept good n := by
  classical
  change traceAverage w n (fun xs => goodFirstIndicator accept good xs) = _
  simp_rw [goodFirstIndicator_expansion]
  rw [traceAverage_sum]
  unfold goodFirstMass
  apply Finset.sum_congr rfl
  intro s _
  by_cases hg : good s = true
  · simpa [hg] using firstAccepted_law w accept hw n (some s)
  · simp [hg, traceAverage_const w hw]

end

/-! A finite exact replacement for uniform real thresholds. A list of real
thresholds subdivides [0,1]. Each resulting interval is an atom with weight its
length. Every inserted threshold has exactly its stated acceptance mass. -/

structure ThresholdInterval where
  lo : ℝ
  hi : ℝ
  valid : lo ≤ hi

def splitPoint (I : ThresholdInterval) (t : ℝ) : ℝ := max I.lo (min t I.hi)

def splitLeft (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨I.lo, splitPoint I t, le_max_left _ _⟩

def splitRight (I : ThresholdInterval) (t : ℝ) : ThresholdInterval :=
  ⟨splitPoint I t, I.hi, max_le I.valid (min_le_right _ _)⟩

def cutAt (r : ℝ) (I : ThresholdInterval) : Prop := I.hi ≤ r ∨ r ≤ I.lo

def intervalCDF (r : ℝ) (I : ThresholdInterval) : ℝ := min r I.hi - min r I.lo

theorem split_cdf (I : ThresholdInterval) (t r : ℝ) :
    intervalCDF r (splitLeft I t) + intervalCDF r (splitRight I t) = intervalCDF r I := by
  unfold intervalCDF splitLeft splitRight
  ring

theorem accepted_interval_mass (I : ThresholdInterval) (r : ℝ) (hc : cutAt r I) :
    (if I.lo < r then I.hi - I.lo else 0) = intervalCDF r I := by
  by_cases hl : I.lo < r
  · have hu : I.hi ≤ r := hc.resolve_right (not_le_of_gt hl)
    simp [hl, intervalCDF, min_eq_right hu, min_eq_right (le_of_lt hl)]
  · have hr : r ≤ I.lo := le_of_not_gt hl
    simp [hl, intervalCDF, min_eq_left hr, min_eq_left (hr.trans I.valid)]

theorem splitLeft_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitLeft I t) := by
  by_cases h : I.lo ≤ t
  · exact Or.inl (max_le h (min_le_left _ _))
  · exact Or.inr (le_of_lt (lt_of_not_ge h))

theorem splitRight_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitRight I t) := by
  by_cases h : t ≤ I.hi
  · right
    change t ≤ max I.lo (min t I.hi)
    rw [min_eq_left h]
    exact le_max_right _ _
  · exact Or.inl (le_of_lt (lt_of_not_ge h))

theorem splitLeft_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitLeft I t) := by
  rcases h with h | h
  · exact Or.inl ((max_le I.valid (min_le_right _ _)).trans h)
  · exact Or.inr h

theorem splitRight_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitRight I t) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (le_max_left _ _))

def splitAll (t : ℝ) : List ThresholdInterval → List ThresholdInterval
  | [] => []
  | I :: rest => splitLeft I t :: splitRight I t :: splitAll t rest

def unitThresholdInterval : ThresholdInterval := ⟨0, 1, by norm_num⟩

def thresholdPartition : List ℝ → List ThresholdInterval
  | [] => [unitThresholdInterval]
  | t :: rest => splitAll t (thresholdPartition rest)

def sumOnIntervals (f : ThresholdInterval → ℝ) : List ThresholdInterval → ℝ
  | [] => 0
  | I :: rest => f I + sumOnIntervals f rest

theorem sumOn_splitAll (f : ThresholdInterval → ℝ) (t : ℝ)
    (hf : ∀ I, f (splitLeft I t) + f (splitRight I t) = f I)
    (intervals : List ThresholdInterval) :
    sumOnIntervals f (splitAll t intervals) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => rfl
  | cons I rest ih =>
      simp only [splitAll, sumOnIntervals, ih]
      rw [← add_assoc, hf]

theorem partition_sum (f : ThresholdInterval → ℝ)
    (hf : ∀ t I, f (splitLeft I t) + f (splitRight I t) = f I)
    (thresholds : List ℝ) :
    sumOnIntervals f (thresholdPartition thresholds) = f unitThresholdInterval := by
  induction thresholds with
  | nil => simp [thresholdPartition, sumOnIntervals]
  | cons t rest ih =>
      rw [thresholdPartition, sumOn_splitAll f t (hf t), ih]

theorem partition_total_mass (thresholds : List ℝ) :
    sumOnIntervals (fun I => I.hi - I.lo) (thresholdPartition thresholds) = 1 := by
  have h := partition_sum (fun I => I.hi - I.lo)
    (fun t I => by simp only [splitLeft, splitRight]; ring) thresholds
  simpa [unitThresholdInterval] using h

theorem partition_cdf (thresholds : List ℝ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) = r := by
  have h := partition_sum (intervalCDF r) (fun t I => split_cdf I t r) thresholds
  simpa [intervalCDF, unitThresholdInterval, min_eq_left h1, min_eq_right h0] using h

theorem splitAll_new_cuts (intervals : List ThresholdInterval) (t : ℝ) :
    ∀ I ∈ splitAll t intervals, cutAt t I := by
  induction intervals with
  | nil => intro I h; simp [splitAll] at h
  | cons J rest ih =>
      intro I h
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_cut J t
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_cut J t
        · exact ih I h

theorem splitAll_preserves_cuts (intervals : List ThresholdInterval) (t r : ℝ) :
    (∀ I ∈ intervals, cutAt r I) → ∀ I ∈ splitAll t intervals, cutAt r I := by
  induction intervals with
  | nil => intro _ I h; simp [splitAll] at h
  | cons J rest ih =>
      intro hc I h
      have hJ : cutAt r J := hc J (by simp)
      have hrest : ∀ K ∈ rest, cutAt r K := fun K hK => hc K (by simp [hK])
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_preserves_cut J t r hJ
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_preserves_cut J t r hJ
        · exact ih hrest I h

theorem partition_cuts (thresholds : List ℝ) (r : ℝ) :
    r ∈ thresholds → ∀ I ∈ thresholdPartition thresholds, cutAt r I := by
  induction thresholds with
  | nil => intro hr; simp at hr
  | cons t rest ih =>
      intro hr
      rcases List.mem_cons.mp hr with h | h
      · subst r; exact splitAll_new_cuts (thresholdPartition rest) t
      · exact splitAll_preserves_cuts (thresholdPartition rest) t r (ih h)

theorem sumOnIntervals_congr (f g : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∀ I ∈ intervals, f I = g I) → sumOnIntervals f intervals = sumOnIntervals g intervals := by
  induction intervals with
  | nil => intro _; rfl
  | cons J rest ih =>
      intro h
      have hJ := h J (by simp)
      have hr : ∀ I ∈ rest, f I = g I := fun I hI => h I (by simp [hI])
      simp only [sumOnIntervals, hJ, ih hr]

theorem partition_acceptance_mass (thresholds : List ℝ) (r : ℝ)
    (hr : r ∈ thresholds) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (fun I => if I.lo < r then I.hi - I.lo else 0)
      (thresholdPartition thresholds) = r := by
  calc
    _ = sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) :=
      sumOnIntervals_congr _ _ _ (fun I hI =>
        accepted_interval_mass I r (partition_cuts thresholds r hr I hI))
    _ = r := partition_cdf thresholds r h0 h1

theorem sum_interval_get (f : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∑ i : Fin intervals.length, f intervals[i]) = sumOnIntervals f intervals := by
  induction intervals with
  | nil => simp [sumOnIntervals]
  | cons I rest ih =>
      simpa [Fin.sum_univ_succ, sumOnIntervals] using congrArg (fun x : ℝ => f I + x) ih

/-! An actual finite probability rectangle implementing all thresholds from a
fixed finite list. The seed distribution is shared; each local acceptance test
depends only on its own density. -/

variable {α : Type*} [Fintype α]

theorem sum_div_const_inline_Rectangle {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    (∑ i, f i) / c = ∑ i, f i / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

abbrev RectangleSeed (thresholds : List ℝ) (α : Type*) :=
  α × Fin (thresholdPartition thresholds).length

def rectangleWeight (thresholds : List ℝ) (seed : RectangleSeed thresholds α) : ℝ :=
  ((thresholdPartition thresholds)[seed.2].hi - (thresholdPartition thresholds)[seed.2].lo) /
    (Fintype.card α : ℝ)

def rectangleAccept (thresholds : List ℝ) (density : α → ℝ)
    (seed : RectangleSeed thresholds α) : Bool :=
  decide ((thresholdPartition thresholds)[seed.2].lo < density seed.1)

theorem rectangleWeight_nonnegative (thresholds : List ℝ) (seed : RectangleSeed thresholds α) :
    0 ≤ rectangleWeight thresholds seed :=
  div_nonneg (sub_nonneg.mpr ((thresholdPartition thresholds)[seed.2].valid)) (by positivity)

theorem rectangleWeight_normalized [Nonempty α] (thresholds : List ℝ) :
    ∑ seed : RectangleSeed thresholds α, rectangleWeight thresholds seed = 1 := by
  rw [Fintype.sum_prod_type]
  have hrow (a : α) : (∑ i, rectangleWeight thresholds (a, i)) =
      1 / (Fintype.card α : ℝ) := by
    unfold rectangleWeight
    rw [← sum_div_const_inline_Rectangle, sum_interval_get (fun I => I.hi - I.lo), partition_total_mass]
  simp_rw [hrow]
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [hc]

theorem rectangle_row_mass (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : density a ∈ thresholds) (h0 : 0 ≤ density a) (h1 : density a ≤ 1) :
    (∑ i, if rectangleAccept thresholds density (a, i) then
      rectangleWeight thresholds (a, i) else 0) = density a / (Fintype.card α : ℝ) := by
  calc
    _ = (∑ i : Fin (thresholdPartition thresholds).length,
        if (thresholdPartition thresholds)[i].lo < density a then
          (thresholdPartition thresholds)[i].hi - (thresholdPartition thresholds)[i].lo else 0) /
        (Fintype.card α : ℝ) := by
      rw [sum_div_const_inline_Rectangle]
      apply Finset.sum_congr rfl
      intro i _
      simp [rectangleAccept, rectangleWeight, ite_div]
    _ = density a / (Fintype.card α : ℝ) := by
      rw [sum_interval_get (fun I => if I.lo < density a then I.hi - I.lo else 0),
        partition_acceptance_mass thresholds (density a) hm h0 h1]

theorem rectangle_acceptance_mass (thresholds : List ℝ) (density : α → ℝ)
    (hm : ∀ a, density a ∈ thresholds) (h0 : ∀ a, 0 ≤ density a)
    (h1 : ∀ a, density a ≤ 1) :
    eventMass (rectangleWeight thresholds) (rectangleAccept thresholds density) =
      (∑ a, density a) / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  simp_rw [rectangle_row_mass thresholds density _ (hm _) (h0 _) (h1 _)]
  rw [sum_div_const_inline_Rectangle]

omit [Fintype α] in theorem rectangle_and (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => min (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

theorem min_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : min x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [min_def, h, hx, hy]

end MaxCutGames.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_LabelBound
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

def localSample (accept : σ → Bool) (decode : σ → α) (fallback : α)
    (proposals : List σ) : α :=
  ((firstAccepted accept proposals).map decode).getD fallback

end

/-!
A single finite rectangle proposal law for two finite families of distributions.
The subdivision includes every density appearing in either family.  Consequently
the local samplers share a seed space independently of their particular inputs.
-/

open scoped BigOperators

end MaxCutGames.Foundations.CorrelatedSampling

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

/-! Exact finite total variation and its event-probability bound. -/

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Overlap
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

universe u

def TraceSeed (σ : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => σ × TraceSeed σ n

instance traceSeedFintype {σ : Type*} [Fintype σ] (n : Nat) : Fintype (TraceSeed σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (σ × TraceSeed σ n))

instance traceSeedUniqueZero {σ : Type*} : Unique (TraceSeed σ 0) :=
  inferInstanceAs (Unique PUnit)

def traceList {σ : Type*} : (n : Nat) → TraceSeed σ n → List σ
  | 0, _ => []
  | n + 1, seed => seed.1 :: traceList n seed.2

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

open MaxCutGames.Foundations.CorrelatedSampling
open MaxCutGames.Foundations.Repetition
open scoped BigOperators

variable {V S A : Type*} [Fintype V] [Fintype S] [Fintype A]

def partialSample (accept : V → S → Bool) (label : V → S → A)
    (fallback : A) (proposals : List S) (v : V) : A :=
  localSample (accept v) (label v) fallback proposals

omit [Fintype V] [Fintype S] [Fintype A] in
theorem first_good_relation_le_inline_RoundingSampling (accept : V → S → Bool)
    (label : V → S → A) (R : V → V → A → A → Bool)
    (fallback : A) (x y : V) (proposals : List S) :
    goodFirstIndicator (fun s => accept x s || accept y s)
      (fun s => accept x s && accept y s && R x y (label x s) (label y s)) proposals ≤
    (if R x y (partialSample accept label fallback proposals x)
      (partialSample accept label fallback proposals y) then 1 else 0) := by
  classical
  cases hfirst : firstAccepted (fun s => accept x s || accept y s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      split <;> norm_num
  | some s =>
      by_cases hg : (accept x s && accept y s && R x y (label x s) (label y s)) = true
      · have hp : (accept x s = true ∧ accept y s = true) ∧
            R x y (label x s) (label y s) = true := by simpa using hg
        have hs := first_union_common (accept x) (accept y) proposals s hfirst hp.1.1 hp.1.2
        simp [goodFirstIndicator, hfirst, partialSample, localSample,
          hs.1, hs.2, hp.1.1, hp.1.2, hp.2]
      · simp only [goodFirstIndicator, hfirst, hg, Bool.false_eq_true, ite_false]
        split <;> norm_num

theorem partial_ratio_bound_inline_RoundingSampling {g u density : ℝ} (hdensity : 0 < density)
    (hg : 0 ≤ g) (_hgl : g ≤ density) (hlu : density ≤ u) (hug : u + g ≤ 2 * density) :
    2 * (g / density) - 1 ≤ g / u := by
  have hu : 0 < u := lt_of_lt_of_le hdensity hlu
  apply (le_div_iff₀ hu).2
  by_cases hsgn : 2 * (g / density) - 1 ≤ 0
  · exact (mul_nonpos_of_nonpos_of_nonneg hsgn hu.le).trans hg
  · have hcoeff : 0 ≤ 2 * g - density := by
      have hd : 1 < 2 * g / density := by
        rw [mul_div_assoc]
        linarith
      have := (lt_div_iff₀ hdensity).mp hd
      linarith
    have hm := mul_le_mul_of_nonneg_left hug hcoeff
    have heq : (2 * (g / density) - 1) * u = ((2 * g - density) * u) / density := by
      field_simp [ne_of_gt hdensity]

    rw [heq]
    apply (div_le_iff₀ hdensity).2
    nlinarith [sq_nonneg (density - g)]

end

/-!
Exact finite threshold expansion for unit vectors.  A shared seed chooses one
coordinate and one atom of the common threshold partition.  Squared amplitudes
are acceptance probabilities, and joint acceptance has the coordinatewise
minimum law.  The construction permits arbitrary vertex-dependent labels and
arbitrary relations between their labels.
-/

open scoped BigOperators
open Foundations CorrelatedSampling

variable {V Ω A : Type*} [Fintype V] [Fintype Ω]

/-- All squared amplitudes, including repetitions, determine a single shared
finite threshold partition. -/
def thresholdLevels (f : V → Ω → ℝ) : List ℝ := by
  classical
  exact (Finset.univ : Finset (V × Ω)).toList.map (fun p => f p.1 p.2 ^ 2)

theorem square_mem_thresholdLevels (f : V → Ω → ℝ) (x : V) (ω : Ω) :
    f x ω ^ 2 ∈ thresholdLevels f := by
  classical
  apply List.mem_map.mpr
  exact ⟨(x, ω), by simp, rfl⟩

/-- The seed is a coordinate and a finite threshold interval. -/
abbrev ThresholdSeed (f : V → Ω → ℝ) := RectangleSeed (thresholdLevels f) Ω

def thresholdAccept (f : V → Ω → ℝ) (x : V) : ThresholdSeed f → Bool :=
  rectangleAccept (thresholdLevels f) (fun ω => f x ω ^ 2)

/-- Labels use only the local vertex and the shared coordinate. -/
def thresholdLabel (f : V → Ω → ℝ) (a : V → Ω → A) (x : V)
    (seed : ThresholdSeed f) : A := a x seed.1

def thresholdRate (Ω : Type*) [Fintype Ω] : ℝ := 1 / Fintype.card Ω

theorem thresholdRate_positive [Nonempty Ω] : 0 < thresholdRate Ω := by
  unfold thresholdRate
  exact one_div_pos.mpr (by exact_mod_cast Fintype.card_pos (α := Ω))

omit [Fintype V] in
theorem square_le_one_of_row_norm (f : V → Ω → ℝ)
    (hnorm : ∀ x, ∑ ω, f x ω ^ 2 = 1) (x : V) (ω : Ω) : f x ω ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ t, f x t ^ 2 :=
      Finset.single_le_sum (fun t _ => sq_nonneg (f x t)) (Finset.mem_univ ω)
    _ = 1 := hnorm x

end MaxCutGames.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scalar parameter selection for the v2 repetition rate.

These results concern powers of real numbers only. In particular, they do not
assert a parallel-repetition theorem for games. The exponent depends only on
the gap and the desired error; no alphabet or logical dimension occurs here.
-/

namespace MaxCutGames.Repetition

/-- The scalar rate appearing in the alphabet-independent repetition estimate. -/
noncomputable def dsRate (gap : ℝ) : ℝ := 1 - gap ^ 2 / 16

theorem dsRate_nonneg {gap : ℝ} (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1) :
    0 ≤ dsRate gap := by
  dsimp [dsRate]
  nlinarith

end MaxCutGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_AnalyticCheeger
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

namespace MaxCutGames.Repetition.Analytic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def quadraticMass (w f g : ι → ℝ) : ℝ :=
  ∑ i, w i * ((f i) ^ 2 + (g i) ^ 2) / 2

def gatedCorrelation (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * f i * g i else 0

def gatedMinimum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * min ((f i) ^ 2) ((g i) ^ 2) else 0

def gatedMaximum (w f g : ι → ℝ) (gate : ι → Bool) : ℝ :=
  ∑ i, if gate i then w i * max ((f i) ^ 2) ((g i) ^ 2) else 0

theorem gatedCorrelation_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    0 ≤ gatedCorrelation w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (mul_nonneg (hw i) (hf i)) (hg i)
  · exact le_rfl

theorem gatedCorrelation_le_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : gatedCorrelation w f g gate ≤ quadraticMass w f g := by
  apply Finset.sum_le_sum
  intro i _
  split
  · have hfg : f i * g i ≤ ((f i) ^ 2 + (g i) ^ 2) / 2 := by
      nlinarith [sq_nonneg (f i - g i)]
    simpa only [← mul_assoc, mul_div_assoc] using mul_le_mul_of_nonneg_left hfg (hw i)
  · exact div_nonneg (mul_nonneg (hw i) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (by norm_num)

theorem gatedMinimum_nonnegative (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ gatedMinimum w f g gate := by
  apply Finset.sum_nonneg
  intro i _
  split
  · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
  · exact le_rfl

theorem gatedMinimum_add_maximum_le (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedMinimum w f g gate + gatedMaximum w f g gate ≤ 2 * quadraticMass w f g := by
  unfold gatedMinimum gatedMaximum quadraticMass
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gate i = true
  · simp only [hi, ↓reduceIte]
    have h := min_add_max ((f i) ^ 2) ((g i) ^ 2)
    rw [← mul_add, h]
    ring_nf ; exact le_rfl
  · simp only [hi, Bool.false_eq_true, ↓reduceIte, zero_add]
    have := hw i
    positivity

/-- A gated finite Cauchy--Schwarz estimate. This is the algebraic heart of
the threshold-rounding inequality, with no independence assumption. -/
theorem gatedCorrelation_sq_le_min_mul_max (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate * gatedMaximum w f g gate := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _
    split
    · exact mul_nonneg (hw i) (le_min (sq_nonneg _) (sq_nonneg _))
    · exact le_rfl
  · intro i _
    split
    · exact mul_nonneg (hw i) ((sq_nonneg (f i)).trans (le_max_left _ _))
    · exact le_rfl
  · intro i _
    by_cases hi : gate i = true
    · simp only [hi, ↓reduceIte]
      rcases le_total ((f i) ^ 2) ((g i) ^ 2) with h | h
      · rw [min_eq_left h, max_eq_right h]
        ring_nf ; exact le_rfl
      · rw [min_eq_right h, max_eq_left h]
        ring_nf ; exact le_rfl
    · simp [hi]

theorem gatedCorrelation_sq_le_min_quadratic (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) :
    gatedCorrelation w f g gate ^ 2 ≤
      gatedMinimum w f g gate *
        (2 * quadraticMass w f g - gatedMinimum w f g gate) := by
  have hmax := gatedMinimum_add_maximum_le w f g gate hw
  have hmin := gatedMinimum_nonnegative w f g gate hw
  exact (gatedCorrelation_sq_le_min_mul_max w f g gate hw).trans
    (mul_le_mul_of_nonneg_left (by linarith) hmin)

/-- The near-perfect form suffices for alphabet-independent repetition.
The total squared mass may be at most one, rather than exactly one. -/
theorem gatedMinimum_near_one (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) {η : ℝ} (_hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hmass : quadraticMass w f g ≤ 1)
    (hcorrelation : 1 - η ≤ gatedCorrelation w f g gate) :
    1 - Real.sqrt (2 * η) ≤ gatedMinimum w f g gate := by
  have hmin := gatedMinimum_nonnegative w f g gate hw
  have h := gatedCorrelation_sq_le_min_quadratic w f g gate hw
  have hcorr : 0 ≤ gatedCorrelation w f g gate := by linarith
  have hsqcorr : (1 - η) ^ 2 ≤ gatedCorrelation w f g gate ^ 2 := by
    nlinarith
  have hupper : gatedMinimum w f g gate *
      (2 * quadraticMass w f g - gatedMinimum w f g gate) ≤
      gatedMinimum w f g gate * (2 - gatedMinimum w f g gate) := by
    apply mul_le_mul_of_nonneg_left _ hmin
    linarith
  have hsq : (1 - gatedMinimum w f g gate) ^ 2 ≤ 2 * η := by
    nlinarith [sq_nonneg η]
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  linarith

/-- Unit-mass form for the joint question-pair and auxiliary-coordinate law. -/
theorem gatedMinimum_unit_mass (w f g : ι → ℝ) (gate : ι → Bool)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hmass : quadraticMass w f g = 1) :
    1 - Real.sqrt (2 * (1 - gatedCorrelation w f g gate)) ≤
      gatedMinimum w f g gate := by
  have hc₀ := gatedCorrelation_nonnegative w f g gate hw hf hg
  have hc₁ := gatedCorrelation_le_mass w f g gate hw
  rw [hmass] at hc₁
  apply gatedMinimum_near_one w f g gate hw
  · linarith
  · linarith
  · exact hmass.le
  · linarith

end MaxCutGames.Repetition.Analytic

/-! Finite vertex-specific padding of nonnegative vectors to unit squared row
mass. The new coordinates can only increase any nonnegative relation energy. -/

namespace MaxCutGames.Repetition

section

open scoped BigOperators

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

def rowSquareMass (f : V → Ω → ℝ) (v : V) : ℝ := ∑ ω, (f v ω) ^ 2

def paddedAmplitude [DecidableEq V] (f : V → Ω → ℝ) (v : V) : Ω ⊕ V → ℝ
  | Sum.inl ω => f v ω
  | Sum.inr w => if v = w then Real.sqrt (1 - rowSquareMass f v) else 0

def paddedLabel (a : V → Ω → A) (fallback : A) (v : V) : Ω ⊕ V → A
  | Sum.inl ω => a v ω
  | Sum.inr _ => fallback

omit [Fintype V] in
theorem paddedAmplitude_nonnegative [DecidableEq V] (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (v : V) (ω : Ω ⊕ V) :
    0 ≤ paddedAmplitude f v ω := by
  cases ω with
  | inl ω => exact hf v ω
  | inr w =>
      simp only [paddedAmplitude]
      split
      · exact Real.sqrt_nonneg _
      · exact le_rfl

end

/-! Flatten the genuine finite occurrence law together with the auxiliary
coordinate into the Cheeger inequality. The occurrence may retain hidden
information; both endpoint label tables still depend only on their vertex. -/

open scoped BigOperators

end MaxCutGames.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_Rounding
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

/-!
Determinization of a nonnegative vector with one label chosen per vertex.
Every vertex retains its total mass. The objective is an arbitrary nonnegative
weighted sum of squares of linear functionals, so coefficients may have either
sign. Sampling complete label tables gives the original vector as its mean;
finite variance and an attained maximum then supply a deterministic table.
-/

section

open scoped BigOperators

variable {V A T : Type*} [Fintype V] [Fintype A] [Fintype T]

/-- The mass at each vertex, before or after determinization. -/
def rowMass (h : V → A → ℝ) (v : V) : ℝ := ∑ a, h v a

/-- Move the full mass of each row to its selected label. -/
def deterministicVector [DecidableEq A] (h : V → A → ℝ) (labels : V → A)
    (v : V) (a : A) : ℝ :=
  if a = labels v then rowMass h v else 0

omit [Fintype V] in
@[simp] theorem deterministicVector_rowMass [DecidableEq A]
    (h : V → A → ℝ) (labels : V → A) (v : V) :
    rowMass (deterministicVector h labels) v = rowMass h v := by
  simp [rowMass, deterministicVector]

omit [Fintype V] in
theorem rowMass_nonnegative (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a) (v : V) :
    0 ≤ rowMass h v :=
  Finset.sum_nonneg (fun a _ => hh v a)

omit [Fintype V] in
theorem deterministicVector_nonnegative [DecidableEq A] (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (labels : V → A) (v : V) (a : A) :
    0 ≤ deterministicVector h labels v a := by
  unfold deterministicVector
  split
  · exact rowMass_nonnegative h hh v
  · exact le_rfl

@[simp] theorem deterministicVector_linear_image [DecidableEq A]
    (h : V → A → ℝ) (labels : V → A) (c : V → A → ℝ) :
    (∑ v, ∑ a, c v a * deterministicVector h labels v a) =
      ∑ v, c v (labels v) * rowMass h v := by
  simp [deterministicVector, mul_ite]

omit [Fintype V] in
theorem entry_eq_zero_of_rowMass_eq_zero (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (v : V) (hz : rowMass h v = 0) (a : A) :
    h v a = 0 := by
  have hle : h v a ≤ rowMass h v :=
    Finset.single_le_sum (fun b _ => hh v b) (Finset.mem_univ a)
  exact le_antisymm (hz ▸ hle) (hh v a)

end

/-!
Finite conditional projection kernels for the Dinur--Steurer argument.
The outer distribution samples the right question and the inner distribution
samples the left question conditional on it. These are genuine normalized
finite distributions; no norm inequality or repetition claim is a field.
-/

open scoped BigOperators

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def vectorMass (f : Ω → Q₁ → A₁ → ℝ) (x : Q₁) : ℝ :=
  ∑ ω, (∑ a, f ω x a) ^ 2

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

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

abbrev SymmetricEdge (Q₁ Q₂ : Type*) := Q₂ × Q₁ × Q₁

def symmetricLeft (e : SymmetricEdge Q₁ Q₂) : Q₁ := e.2.1

def symmetricRight (e : SymmetricEdge Q₁ Q₂) : Q₁ := e.2.2

/-- A coordinate has one possible nonzero label at each question. -/
def singleLabelVector (a : Q₁ → Ω → A₁) (f : Q₁ → Ω → ℝ)
    (ω : Ω) (x : Q₁) (b : A₁) : ℝ := by
  classical
  exact if a x ω = b then f x ω else 0

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

/-- The amplitude at a question is the sum of its original label entries. -/
def vectorAmplitude (h : Ω → Q₁ → A₁ → ℝ) (x : Q₁) (ω : Ω) : ℝ :=
  rowMass (h ω) x

omit [Fintype Ω] in
omit [Fintype Q₁] in
theorem vectorAmplitude_nonnegative (h : Ω → Q₁ → A₁ → ℝ)
    (hh : ∀ ω x a, 0 ≤ h ω x a) (x : Q₁) (ω : Ω) :
    0 ≤ vectorAmplitude h x ω :=
  rowMass_nonnegative (h ω) (hh ω) x

omit [Fintype Q₁] in
@[simp] theorem rowSquareMass_vectorAmplitude (h : Ω → Q₁ → A₁ → ℝ) (x : Q₁) :
    rowSquareMass (vectorAmplitude h) x = vectorMass h x := rfl

end MaxCutGames.Repetition.ProjectionKernel

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ProductCollisionBounds
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

/-!
Finite-sum tensor factorization used by projection-game collision operators.
No restriction to coordinatewise strategies occurs: `f` below is an arbitrary
function of both input questions and both input answers.
-/

section

open scoped BigOperators

variable {X A Y B U D Z C I : Type*}
  [Fintype X] [Fintype A] [Fintype U] [Fintype D] [Fintype I]

/-- Apply a finite real kernel. Output indices need no finiteness assumption. -/
def kernelApply (K : Y → B → X → A → ℝ) (f : X → A → ℝ) (y : Y) (b : B) : ℝ :=
  ∑ x, ∑ a, K y b x a * f x a

/-- Independent tensor of two kernels. -/
def tensorKernel (K : Y → B → X → A → ℝ) (L : Z → C → U → D → ℝ)
    (yz : Y × Z) (bc : B × C) (xu : X × U) (ad : A × D) : ℝ :=
  K yz.1 bc.1 xu.1 ad.1 * L yz.2 bc.2 xu.2 ad.2

/-- Applying the tensor first applies `L` separately for every fixed input of
`K`, and then applies `K`. This is valid for arbitrary coupled inputs. -/
theorem kernelApply_tensor
    (K : Y → B → X → A → ℝ) (L : Z → C → U → D → ℝ)
    (f : (X × U) → (A × D) → ℝ) (y : Y) (z : Z) (b : B) (c : C) :
    kernelApply (tensorKernel K L) f (y,z) (b,c) =
      kernelApply K (fun x a => kernelApply L (fun u d => f (x,u) (a,d)) z c) y b := by
  classical
  simp only [kernelApply, tensorKernel, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum, mul_assoc]

/-- Summing a family of input functions commutes with the finite operator. -/
theorem kernelApply_sum
    (K : Y → B → X → A → ℝ) (f : I → X → A → ℝ) (y : Y) (b : B) :
    kernelApply K (fun x a => ∑ i, f i x a) y b =
      ∑ i, kernelApply K (f i) y b := by
  classical
  simp only [kernelApply, Finset.mul_sum]
  calc
    (∑ x, ∑ a, ∑ i, K y b x a * f i x a) =
        ∑ x, ∑ i, ∑ a, K y b x a * f i x a := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem kernelApply_smul
    (K : Y → B → X → A → ℝ) (f : X → A → ℝ) (r : ℝ) (y : Y) (b : B) :
    kernelApply K (fun x a => r * f x a) y b = r * kernelApply K f y b := by
  simp only [kernelApply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_left_comm _ _ _

end
namespace ProjectionKernel

open scoped BigOperators

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Ω I : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Ω] [Fintype I]

/-! Exact tensor identities for normalized finite projection kernels. -/

/-!
The tensor-domination reduction before the Dinur--Steurer rounding theorem.
Every deterministic strategy for the product gives a nonnegative vector table
for the first kernel. Its energy is exactly the product collision energy, and
each input-question mass is bounded by the second kernel's collision value.
-/

/-! Homogeneous normalization for finite nonnegative vector assignments. -/

omit [Fintype Q₁] in
theorem vectorMass_smul (f : Ω → Q₁ → A₁ → ℝ) (r : ℝ) (x : Q₁) :
    vectorMass (fun ω x a => r * f ω x a) x = r ^ 2 * vectorMass f x := by
  unfold vectorMass
  simp_rw [← Finset.mul_sum, mul_pow]
  exact (Finset.mul_sum _ _ _).symm

omit [Fintype Q₁] in
theorem entry_eq_zero_of_vectorMass_nonpositive
    (f : Ω → Q₁ → A₁ → ℝ) (hf : ∀ ω x a, 0 ≤ f ω x a)
    (hmass : ∀ x, vectorMass f x ≤ 0) (ω : Ω) (x : Q₁) (a : A₁) :
    f ω x a = 0 := by
  classical
  have hsquare : (∑ b, f ω x b) ^ 2 ≤ vectorMass f x :=
    Finset.single_le_sum (fun τ _ => sq_nonneg (∑ b, f τ x b)) (Finset.mem_univ ω)
  have hsum : ∑ b, f ω x b = 0 := by
    nlinarith [hmass x, sq_nonneg (∑ b, f ω x b)]
  have hentry : f ω x a ≤ ∑ b, f ω x b :=
    Finset.single_le_sum (fun b _ => hf ω x b) (Finset.mem_univ a)
  rw [hsum] at hentry
  exact le_antisymm hentry (hf ω x a)

/-!
Collision norms are unchanged by bijective encodings of either player's
questions and answers. The distributions, acceptance predicate, and assignment
tables are transported together. This provides the finite-tuple regrouping
needed to pass from one product step to arbitrary parallel repetition.
-/

end ProjectionKernel

end

end MaxCutGames.Repetition

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_KernelIteration
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

namespace MaxCutGames.Repetition

theorem sequence_le_power {r : ℝ} (hr : 0 ≤ r) (c : ℕ → ℝ)
    (hzero : c 0 ≤ 1) (hstep : ∀ n, c (n + 1) ≤ r * c n) :
    ∀ n, c n ≤ r ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      calc
        c (n + 1) ≤ r * c n := hstep n
        _ ≤ r * r ^ n := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem squared_rate_le_dsRate_sq {gap : ℝ}
    (_hgap₀ : 0 ≤ gap) (_hgap₁ : gap ≤ 1) :
    1 - gap ^ 2 / 8 ≤ dsRate gap ^ 2 := by
  dsimp [dsRate]
  nlinarith only [sq_nonneg (gap ^ 2)]

theorem rate_of_squared_collision_recurrence {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (c v : ℕ → ℝ) (hzero : c 0 ≤ 1)
    (hstep : ∀ n, c (n + 1) ≤ (1 - gap ^ 2 / 8) * c n)
    (hvalue : ∀ n, v n ^ 2 ≤ c n) :
    ∀ n, v n ≤ dsRate gap ^ n := by
  have hr : 0 ≤ 1 - gap ^ 2 / 8 := by nlinarith
  have hpow := sequence_le_power hr c hzero hstep
  intro n
  apply le_of_sq_le_sq _ (pow_nonneg (dsRate_nonneg hgap₀ hgap₁) n)
  calc
    v n ^ 2 ≤ c n := hvalue n
    _ ≤ (1 - gap ^ 2 / 8) ^ n := hpow n
    _ ≤ (dsRate gap ^ 2) ^ n :=
      pow_le_pow_left₀ hr (squared_rate_le_dsRate_sq hgap₀ hgap₁) n
    _ = (dsRate gap ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end MaxCutGames.Repetition

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
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubroutine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual lookup from a preserved table. A fresh copy is prefixed to the scan
stack before each access. The old scan suffix is retained and need not be
cleared between accesses. No graph/table data occurs in finite control. -/

namespace MaxCutGames.Foundations.Complexity.MachineAffineLookup

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

end MaxCutGames.Foundations.Complexity.MachineAffineLookup

/-!
A fixed-width gather from an input-resident table. Every coordinate index lives
on a unary tape. The coefficient and coordinate-dependent offsets alone live
in finite control. Actual preserving affine lookup instructions read each
requested field, and the proof below composes their traces. This is the gather
phase of product-row construction, before the fixed-width Horner phase.
-/

namespace MaxCutGames.Explicit.MachineProductGather

open Turing
open MaxCutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

/-- Shared original table, query, scan and copy scratch, then input coordinate
fields and the corresponding gathered output fields. -/
abbrev Tape (width : Nat) := Fin 4 ⊕ (Fin width ⊕ Fin width)

def shift (width : Nat) : Tape width → Tape (width + 1) :=
  Sum.map id (Sum.map Fin.succ Fin.succ)

theorem shift_injective (width : Nat) : Function.Injective (shift width) := by
  intro a b h
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;> simp_all [shift]

def lookupRole (width : Nat) : Fin 5 → Tape (width + 1)
  | 0 => .inl 0
  | 1 => .inl 1
  | 2 => .inl 2
  | 3 => .inr (.inr 0)
  | 4 => .inl 3

theorem lookupRole_injective (width : Nat) : Function.Injective (lookupRole width) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [lookupRole]

end MaxCutGames.Explicit.MachineProductGather

/-!
Counted loops in one actual TM2 program. A unary guard is executed once before
each caller body and once more at zero. The caller supplies only individual
body traces, each returning to the guard with the same counter remainder.

Schedules are indexed by the remaining count: body `r` takes ambient state
`r + 1` to ambient state `r`. Consequently the run starts at index `n` and
ends at index zero. Bodies may change the ambient state and unprotected tapes.
-/

namespace MaxCutGames.Foundations.Complexity.MachineCountedLoop

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

/-- Exactly `n` supplied body blocks and `n + 1` concrete guard transitions. -/
def totalSteps (cost : Nat → Nat) (n : Nat) : Nat :=
  (∑ r ∈ Finset.range n, cost r) + n + 1

@[simp] theorem totalSteps_zero (cost : Nat → Nat) : totalSteps cost 0 = 1 := by
  simp [totalSteps]

theorem totalSteps_succ (cost : Nat → Nat) (n : Nat) :
    totalSteps cost (n + 1) = (totalSteps cost n + cost n) + 1 := by
  simp only [totalSteps, Finset.sum_range_succ]
  omega

theorem totalSteps_le (cost : Nat → Nat) (n B : Nat)
    (bodyBound : ∀ r, r < n → cost r ≤ B) :
    totalSteps cost n ≤ n * (B + 1) + 1 := by
  have hsum : (∑ r ∈ Finset.range n, cost r) ≤ n * B := by
    calc
      (∑ r ∈ Finset.range n, cost r) ≤ ∑ _r ∈ Finset.range n, B :=
        Finset.sum_le_sum (fun r hr => bodyBound r (Finset.mem_range.mp hr))
      _ = n * B := by simp
  simpa only [totalSteps, Nat.mul_add, Nat.mul_one] using
    Nat.add_le_add_right (Nat.add_le_add_right hsum n) 1

end MaxCutGames.Foundations.Complexity.MachineCountedLoop

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineUnaryMultiply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
An actual five-stack unary multiplication subroutine. Both isolated input
fields are preserved. The product field prefixes the previous output stack;
the counter and scratch return empty and all other stacks are framed.
-/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

open Turing
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

def bodySteps (a : ℕ) : ℕ := 3 * (a + 1) + 2
def steps (a b : ℕ) : ℕ := 3 * a * b + 8 * b + 7

theorem totalSteps_eq_inline_MachineUnaryMultiply (a b : ℕ) :
    MachineCountedLoop.totalSteps (fun _ => bodySteps a) b = b * (bodySteps a + 1) + 1 := by
  simp [MachineCountedLoop.totalSteps, Nat.mul_add, Nat.add_assoc]

end MaxCutGames.Foundations.Complexity.MachineUnaryMultiply

/-!
One actual Horner step on unary field stacks. Multiplication and addition are
executions of the same finite program. All three operands are preserved; only
the output stack receives a new field and both work stacks return empty.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRadixStep

open Turing

variable {K Λ σ : Type}

variable [DecidableEq K]

def steps (radix acc digit : ℕ) : ℕ := 3 * radix * acc + 8 * acc + 3 * digit + 13

end MaxCutGames.Foundations.Complexity.MachineRadixStep

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineHorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Fixed-width Horner traversal by actual radix steps. Two accumulators alternate:
a radix step writes into the empty alternate, then the previous accumulator is
consumed. The base, digit fields, and arbitrary external tapes are preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineHorner

open Turing

variable {K Λ σ : Type} {width : Nat}

variable [DecidableEq K]

def stepCost (radix acc digit : Nat) : Nat :=
  MachineRadixStep.steps radix acc digit + acc + 1

def perDigitBound (width magnitude : Nat) : Nat :=
  3 * magnitude * (magnitude + 1) ^ width + 9 * (magnitude + 1) ^ width + 3 * magnitude + 14

omit [DecidableEq K] in
theorem stepCost_le (radix acc digit width magnitude : Nat)
    (radixBound : radix ≤ magnitude) (accBound : acc ≤ (magnitude + 1) ^ width)
    (digitBound : digit ≤ magnitude) :
    stepCost radix acc digit ≤ perDigitBound width magnitude := by
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 3 radixBound) accBound
  unfold stepCost MachineRadixStep.steps perDigitBound
  omega

noncomputable def timePolynomial (width : Nat) : Polynomial Nat :=
  Polynomial.C width *
    (3 * Polynomial.X * (Polynomial.X + 1) ^ width +
      9 * (Polynomial.X + 1) ^ width + 3 * Polynomial.X + 14) +
    2 * (Polynomial.X + 1) ^ width + 5

open scoped BigOperators

end MaxCutGames.Foundations.Complexity.MachineHorner

/-! One actual product-output field: gather the fixed number of coordinate
values from the input table, evaluate their common-radix code by Horner, move
the resulting word into the reversed output accumulator, and clear the gather
work. All input fields and the input table are preserved. -/

namespace MaxCutGames.Explicit.MachineProductField

open Turing
open MaxCutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

/-- Gather's table/query/scan/scratch and coordinate tapes; then radix, two
Horner accumulators, counter, scratch, isolated field output, global output. -/
abbrev Layout (width : Nat) := MachineProductGather.Tape width ⊕ Fin 7

def gatherSlots (slots : Layout width ↪ K) : MachineProductGather.Tape width ↪ K :=
  Function.Embedding.trans (Function.Embedding.inl) slots

def clearTapes (slots : Layout width ↪ K) : List K :=
  [slots (.inl (.inl 1)), slots (.inl (.inl 2))] ++
    List.ofFn (fun i : Fin width => slots (.inl (.inr (.inr i))))

/-- Conditions on real input/work stacks; arbitrary output suffixes remain
permitted. The two query/scan tapes are empty at a row boundary. -/
structure Ready (slots : Layout width ↪ K) (base : K → List Bool) : Prop where
  query : base (slots (.inl (.inl 1))) = []
  scan : base (slots (.inl (.inl 2))) = []
  gatherScratch : base (slots (.inl (.inl 3))) = []
  fields : ∀ i, base (slots (.inl (.inr (.inr i)))) = []
  accA : base (slots (.inr 1)) = []
  accB : base (slots (.inr 2)) = []
  counter : base (slots (.inr 3)) = []
  hornerScratch : base (slots (.inr 4)) = []
  output : base (slots (.inr 5)) = []

end MaxCutGames.Explicit.MachineProductField

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

abbrev Label {q : Nat} (cells : List (Fin q × Fin q)) := Fin (cells.length + 1) × Fin 7

def labelAt {q : Nat} (cells : List (Fin q × Fin q)) (r : Nat) (phase : Fin 7) : Label cells :=
  (⟨min r cells.length, by omega⟩, phase)

def pairTime {q : Nat} (words : Fin q → List Bool) (pair : Fin q × Fin q) : Nat :=
  2 * ((words pair.1).length + 1) + 2 * ((words pair.2).length + 1) +
    max (words pair.1).length (words pair.2).length + 2

def prefixTime {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) : Nat :=
  ((cells.take r).map (pairTime words)).sum

theorem prefixTime_succ {q : Nat} (words : Fin q → List Bool)
    (cells : List (Fin q × Fin q)) (r : Nat) (hr : r < cells.length) :
    prefixTime words cells (r + 1) = prefixTime words cells r + pairTime words cells[r] := by
  unfold prefixTime
  rw [List.take_succ_eq_append_getElem hr, List.map_append, List.sum_append]
  rfl

def allPairs (q : Nat) : List (Fin q × Fin q) :=
  (List.finRange q).flatMap fun i => (List.finRange q).map fun j => (i, j)

theorem mem_allPairs {q : Nat} (i j : Fin q) : (i, j) ∈ allPairs q := by
  simp [allPairs]

theorem length_allPairs (q : Nat) : (allPairs q).length = q * q := by
  simp [allPairs, List.length_flatMap]

theorem pairTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (pair : Fin q × Fin q) :
    pairTime words pair ≤ 5 * L + 6 := by
  have hi := hL pair.1
  have hj := hL pair.2
  have hm := max_le hi hj
  dsimp only [pairTime]
  omega

theorem totalTime_le {q : Nat} (words : Fin q → List Bool) (L : Nat)
    (hL : ∀ i, (words i).length ≤ L) (cells : List (Fin q × Fin q)) :
    (cells.map (pairTime words)).sum ≤ cells.length * (5 * L + 6) := by
  induction cells with
  | nil => simp
  | cons pair rest ih =>
    have hp := pairTime_le words L hL pair
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

end MaxCutGames.Foundations.Complexity.MachineFieldProfile

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

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end MaxCutGames.Foundations.Complexity.MachineRegisterEmit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RuntimeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed natural polynomials are represented by literal Horner coefficients.
The coefficient representation is independent of the machine input. The actual
machine wrapper is built from the shared physical unary Horner subroutine. -/

namespace MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable section

def prefixValuePolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => Polynomial.X * prefixValuePolynomial digits i + Polynomial.C (digits i)

def prefixCostPolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => prefixCostPolynomial digits i +
      Polynomial.C 3 * Polynomial.X * prefixValuePolynomial digits i +
      Polynomial.C 9 * prefixValuePolynomial digits i + Polynomial.C (3 * digits i + 14)

end

end MaxCutGames.Foundations.Complexity.CookLevin.PolynomialMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTupleOdometer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineTupleOdometer

open Turing

variable {K Λ σ : Type} [DecidableEq K]

section AscendingCycle

open scoped BigOperators

def cycleSteps (cost : ℕ → ℕ) (maximum count : ℕ) : ℕ :=
  (∑ r ∈ Finset.range (count + 1), cost r) + count + maximum + 2

theorem cycleSteps_zero_inline_MachineTupleOdometer (cost : ℕ → ℕ) (maximum : ℕ) :
    cycleSteps cost maximum 0 = (maximum + 2) + cost 0 := by
  simp [cycleSteps, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem cycleSteps_succ_inline_MachineTupleOdometer (cost : ℕ → ℕ) (maximum count : ℕ) :
    cycleSteps cost maximum (count + 1) =
      (cycleSteps cost maximum count + 1) + cost (count + 1) := by
  simp only [cycleSteps, Finset.sum_range_succ]
  omega

end AscendingCycle

section Nested

open scoped BigOperators

/-- Explicit caller state and tape endpoints for one level of the nested
loop. Compatibility with its child schedules is checked by their types. -/
structure CycleSchedule (K σ : Type) where
  currentSuffix : List Bool
  remainingSuffix : List Bool
  ambient : ℕ → σ
  register : ℕ → Option Bool
  base : ℕ → K → List Bool

omit [DecidableEq K] in
/-- Exact concrete-counter overhead for a complete positive-radix nesting. -/
def counterOverhead (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => n * (counterOverhead n q + 2)

namespace NestedCycle

variable {n : ℕ}
  {current remaining : ℕ → K}
  {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}

def reverseDigit (d : Fin n) : Fin n := ⟨n - 1 - d.val, by omega⟩

end NestedCycle

omit [DecidableEq K] in
theorem counterOverhead_le (n q : ℕ) (hn : 0 < n) :
    counterOverhead n q ≤ 2 * q * n ^ q := by
  induction q with
  | zero => simp [counterOverhead]
  | succ q ih =>
    have hp : 1 ≤ n ^ q := by apply Nat.one_le_pow; exact hn
    have h := Nat.mul_le_mul_left n (Nat.add_le_add_right ih 2)
    have htwo : 2 ≤ 2 * n ^ q := Nat.mul_le_mul_left 2 hp
    have hinner : 2 * q * n ^ q + 2 ≤ 2 * (q + 1) * n ^ q := by
      rw [Nat.mul_add, Nat.add_mul]
      omega
    exact h.trans (by
      simpa only [counterOverhead, pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using Nat.mul_le_mul_left n hinner)

end Nested

end MaxCutGames.Foundations.Complexity.MachineTupleOdometer

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

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

end MaxCutGames.Foundations.Hastad.SourceOdometerSchedule

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
abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {Λ σ : Type}

/-- Specification only: equality of the original natural values, unless an
earlier step has already detected overflow. -/
def hit (flag : Bool) (x v : Nat) : Nat := if flag = false ∧ x = v then 1 else 0

inductive Label
  | copyFirst | copySecond | headerFirst | headerSecond | row | field | restore
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : Label :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

abbrev Row := Nat × List Nat

def rowWords (r : Row) : List Nat := r.1 :: r.2

def rowsHits (v : Nat) : List Row → Nat
  | [] => 0
  | r :: rs => (if r.1 = v then 1 else 0) + rowsHits v rs

end MaxCutGames.Foundations.Complexity.MachineCloudCount

namespace MaxCutGames.Foundations.Complexity.MachineCeilingPower

open Turing

variable {σ : Type}

def overflow (flag : Bool) (x p : Nat) : Bool := flag || decide (p < x)

theorem appendTrace_inline_MachineCeilingPower {α : Type*} (f : α → α) {a b c : α} {s t : Nat}
    (hs : f^[s] a = b) (ht : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm s t, Function.iterate_add_apply, hs, ht]

def prefixTime (k p : Nat) : Nat := (1 + 2 * (k + 2)) + (k + min k p + 2) + 1

def coreTime (g k : Nat) : Nat → Nat → Nat
  | 0, _ => 3
  | f + 1, p => prefixTime k p +
      if k ≤ p then f + 2 else (p + g * p + 2) + coreTime g k f (p * g)

def roundBudget (g k : Nat) : Nat := (g + 8) * (k + 1) + 16

theorem prefixTime_le (k p : Nat) : prefixTime k p ≤ 4 * k + 8 := by
  have h := Nat.min_le_left k p
  unfold prefixTime
  omega

theorem prefixTime_le_roundBudget (g k p : Nat) : prefixTime k p ≤ roundBudget g k := by
  have h := prefixTime_le k p
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

theorem continuingTime_le (g k p : Nat) (h : p < k) :
    prefixTime k p + (p + g * p + 2) ≤ roundBudget g k := by
  have hprefix := prefixTime_le k p
  have hmul := Nat.mul_le_mul_left g h.le
  unfold roundBudget
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

def totalTime (g k : Nat) : Nat := 1 + 2 * (k + 2) + coreTime g k k 1

def timeBound (g k : Nat) : Nat := (g + 8) * (k + 1) ^ 2 + 18 * (k + 1) + 3

/-- The bound is one fixed quadratic polynomial in the actual unary input
length. Its coefficient may depend on the fixed growth factor. -/
noncomputable def timePolynomial (g : Nat) : Polynomial Nat :=
  Polynomial.C (g + 8) * Polynomial.X ^ 2 + 18 * Polynomial.X + 3

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
abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {σ : Type}

theorem appendTrace_inline_MachineCloudPadding {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end MaxCutGames.Foundations.Complexity.MachineCloudPadding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The executable dummy numbering is the sum of earlier cloud sizes plus
the local dummy index. This connects the actual list search in vertexOrder
with unary prefix-sum routines, without changing the chosen enumeration. -/

namespace MaxCutGames.Foundations.PCP.PreprocessingPaddingOffsets

open scoped BigOperators

theorem idxOf_map_injective_inline_PreprocessingPaddingOffsets {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (xs : List A) (a : A) :
    (xs.map f).idxOf (f a) = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = a
    · subst x; simp
    · simp [List.idxOf_cons_ne, h, hf.ne h, ih]

theorem sigma_idxOf {A : Type*} [DecidableEq A] (sizes : A → Nat)
    (xs : List A) (a : A) (ha : a ∈ xs) (j : Fin (sizes a)) :
    (xs.sigma (fun x => List.finRange (sizes x))).idxOf ⟨a, j⟩ =
      ((xs.take (xs.idxOf a)).map sizes).sum + j.val := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.sigma_cons]
    by_cases h : x = a
    · subst x
      have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∈
          (List.finRange (sizes a)).map (Sigma.mk a) := by
        exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
      rw [List.idxOf_append_of_mem hm,
        idxOf_map_injective_inline_PreprocessingPaddingOffsets (Sigma.mk a) (fun x y h => by cases h; rfl),
        List.idxOf_finRange]
      simp
    · have hm : (⟨a, j⟩ : Σ x, Fin (sizes x)) ∉
          (List.finRange (sizes x)).map (Sigma.mk x) := by
        intro hm
        rcases List.mem_map.mp hm with ⟨k, _, hk⟩
        exact h (congrArg Sigma.fst hk)
      rw [List.idxOf_append_of_notMem hm, List.length_map, List.length_finRange,
        ih (List.mem_of_ne_of_mem (Ne.symm h) ha), List.idxOf_cons_ne xs h]
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

def offset {n : Nat} (padding : Fin n → Nat) (k : Nat) : Nat :=
  (((List.finRange n).take k).map padding).sum

theorem sigma_length {A : Type*} (sizes : A → Nat) (xs : List A) :
    (xs.sigma (fun x => List.finRange (sizes x))).length = (xs.map sizes).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.sigma_cons, ih]

@[simp] theorem offset_zero {n : Nat} (padding : Fin n → Nat) : offset padding 0 = 0 := by
  simp [offset]

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

open Turing
open MaxCutGames.Foundations.PCP
open scoped BigOperators

abbrev State (σ : Type) := (σ × Bool) × Option Bool

variable {σ : Type}

theorem appendTrace_inline_MachineCloudPrefix {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end MaxCutGames.Foundations.Complexity.MachineCloudPrefix

namespace MaxCutGames.Foundations.Complexity.MachineAppendAt

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

end MaxCutGames.Foundations.Complexity.MachineAppendAt

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

section Block

variable {K Λ σ : Type} {N M : Nat}

def finishAt (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

end Block

end MaxCutGames.Foundations.Complexity.MachineFixedBlockMap

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

variable {K Λ σ : Type} [DecidableEq K]

abbrev HeadTapes (K : Type) := Fin 6 → K

noncomputable def headTimePolynomial : Polynomial Nat :=
  Polynomial.C 7 * Polynomial.X + Polynomial.C 5

end MaxCutGames.Foundations.PCP.AlphabetTable.Lookup

/-!
The finite registers and physical tape roles of the alphabet-table machine.
Input-sized numbers occur only on unary tapes. The comparison and emitter
register layouts are related by explicit, executable product rearrangements.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Relations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
# Real gap and exact size of the alphabet graph

The gap bound is obtained directly from the two checked rejection-count
inequalities. The finite graph's size is linear in the old vertices and darts,
with an explicit coefficient determined only by the old alphabet cardinality.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetGraphBounds

open scoped BigOperators

/-- The number of local verifier events for an alphabet with `q` symbols. -/
def localEventFactor (q : Nat) : Nat :=
  4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5

def vertexFactor (q : Nat) : Nat := localEventFactor q + 2 ^ (q * q)

def dartFactor (q : Nat) : Nat := 12 * localEventFactor q

def sizeFactor (q : Nat) : Nat := 2 ^ q + vertexFactor q + dartFactor q

theorem sizeFactor_positive (q : Nat) : 0 < sizeFactor q := by
  have hp : (0 : Nat) < 2 ^ q := pow_pos (by decide) q
  unfold sizeFactor
  omega


end MaxCutGames.Foundations.PCP.AlphabetGraphBounds



end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CompareLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual finite TM2 templates for affine unary fields and finite relation bits.
Commands write in forward bit order onto a stack, so their concatenated result
appears reversed in the accumulator. Every unbounded operand is read from an
isolated unary tape and restored by the checked preserving transducer.
-/

namespace MaxCutGames.Foundations.PCP.AlphabetTable.Emitter

open Turing
open MaxCutGames.Foundations.Complexity

variable {K Λ σ : Type} {h bound : Nat} [DecidableEq K]

def resultTapes (output : K) (base : K → List Bool) (bits : List Bool) : K → List Bool :=
  Function.update base output (bits.reverse ++ base output)

@[simp] theorem resultTapes_output (output : K) (base : K → List Bool) (bits : List Bool) :
    resultTapes output base bits output = bits.reverse ++ base output := by
  simp [resultTapes]

def affineValue (terms : List (Fin h × Nat)) (values : Fin h → Nat) (offset : Nat) : Nat :=
  (terms.map (fun term => term.2 * values term.1)).sum + offset

end MaxCutGames.Foundations.PCP.AlphabetTable.Emitter

/-!
# Affine numeric fields of the alphabet-reduction table

The five unbounded unary inputs are n, m, e, tail, head, in that order.
Every field uses a fixed list of natural coefficients and one bounded offset.
For a fixed local event and slot, the query field's coefficient list does not
depend on the input predicate. The predicate changes only its bounded offset.
Evaluation uses the same `Emitter.affineValue` as the actual unary emitter.
-/

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

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRow

open Turing
open MachineFixedBlockMap
open MaxCutGames.Foundations.PCP

/-! ## Fixed finite relation calculation -/

def inputSize (t S : Nat) : Nat := t * (4096 + (S + S))

/-- The scan order is the fixed increasing finite-index order. -/
def firstMatch {S : Nat} (mask : Fin S → Bool) : Option (Fin S) :=
  (List.ofFn id).find? mask

/-! ## Actual unary Boolean field instructions -/

def encodeBit (b : Bool) : List Bool := if b then [true, false] else [false]

def encodeBits : List Bool → List Bool
  | [] => []
  | b :: bits => encodeBit b ++ encodeBits bits

/-! ## Concrete row machine and its actual one-step execution -/

end MaxCutGames.Foundations.Complexity.PoweringMachineRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineCloudRank

open Turing MachineCloudCount

variable {σ : Type}

inductive RankLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | row | field | restore | done
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def rankSkip (i : Nat) : RankLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .row

/-- In a filtered list, the rank of a retained entry is the number of retained
entries preceding its first original occurrence. This is a specification lemma. -/
theorem idxOf_filter_prefix {α : Type*} [BEq α] [LawfulBEq α]
    (p : α → Bool) (a : α) (hp : p a = true) :
    ∀ xs : List α, a ∈ xs →
      (xs.filter p).idxOf a = ((xs.take (xs.idxOf a)).filter p).length := by
  classical
  intro xs
  induction xs with
  | nil => intro ha; simp at ha
  | cons b xs ih =>
      intro ha
      by_cases hba : b = a
      · subst b
        simp [hp]
      · have ha' : a ∈ xs := by simpa [hba, Ne.symm hba] using ha
        cases hb : p b <;>
          simp [hba, hb, ih ha']

open MaxCutGames.Foundations.PCP

end MaxCutGames.Foundations.Complexity.MachineCloudRank

namespace MaxCutGames.Foundations.Complexity.MachineTableRows

open Turing

inductive Label
  | relationRead | relationRestore | reverseRead | reverseRestore
  | tailRead | tailRestore | appendOld | appendRow | appendBack
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.relationRead, .relationRestore,
  .reverseRead, .reverseRestore, .tailRead, .tailRestore, .appendOld, .appendRow, .appendBack]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- Exact row field concatenation at the level of stored bits. -/
def fieldBits (fields : Fin 3 → K) (base : K → List Bool) : List Bool :=
  base (fields 0) ++ base (fields 1) ++ base (fields 2)

def fieldSize (fields : Fin 3 → K) (base : K → List Bool) : Nat :=
  (base (fields 0)).length + (base (fields 1)).length + (base (fields 2)).length

omit [DecidableEq K] in
@[simp] theorem fieldBits_length (fields : Fin 3 → K) (base : K → List Bool) :
    (fieldBits fields base).length = fieldSize fields base := by
  simp [fieldBits, fieldSize, Nat.add_assoc]

def prefixTapes (fields : Fin 3 → K) (row : K) (base : K → List Bool) : K → List Bool :=
  Function.update base row (fieldBits fields base ++ base row)

end MaxCutGames.Foundations.Complexity.MachineTableRows

/-!
# Machine execution for an inherited regularization row

The machine reads the original reverse index from the physically stored input
table. The unread working copy then starts at the 4096 original predicate
fields; a fixed finite Boolean block copy retains exactly those fields. Unary
arithmetic computes the new reverse index, and the checked row emitter appends
the three physical fields. No input table or unbounded arithmetic function is
stored in the machine's finite state or instructions.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow

open Turing
open PCP

abbrev Tape := Fin 10
abbrev Alphabet (_ : Tape) := Bool

def lookupTape (i : Fin 5) : Tape := ⟨i.val + 1, by omega⟩

theorem lookupTape_injective : Function.Injective lookupTape := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lookupTape] at hv
  omega

theorem source_outside (i : Fin 5) : (0 : Tape) ≠ lookupTape i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [lookupTape] at hv
  omega

def fields : Fin 3 → Tape := Fin.cases 0 (Fin.cases 6 (fun _ => 7))

@[simp] theorem fields_zero : fields 0 = 0 := rfl
@[simp] theorem fields_one : fields 1 = 6 := rfl
@[simp] theorem fields_two : fields 2 = 7 := rfl

theorem fields_separate (i : Fin 3) : fields i ≠ 8 ∧ fields i ≠ 5 := by
  fin_cases i <;> decide

section Execution

variable {Λ σ : Type}

theorem join_trace_inline_MachineRegularOriginalRow {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end Execution

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (4 * q + 17) * inputLength + 2 * outputLength + 4 * q + 32795

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalRow

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

open Turing
open MaxCutGames.Foundations.PCP

inductive Extra | padding | level
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.padding, .level]

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

instance instFintypeExtra : Fintype Extra where
  elems := ⟨Extra.enumList, Extra.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 27 ⊕ Extra
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

/-- Original table, affine query, copied scan, owner output, and scratch. -/
def ownerTapes : Fin 5 → Tape := ![.inl 0, .inl 9, .inl 10, .inl 2, .inl 11]

variable {σ : Type}

/-- Boundary data is a specification of physical tape contents, never part
of the machine's finite control state. All eighteen core work tapes are empty. -/
structure Data where
  table : List Bool
  globalIndex : List Bool
  owner : List Bool
  localRank : List Bool
  count : List Bool
  offset : List Bool
  darts : List Bool
  rotor : List Bool
  output : List Bool
  padding : List Bool
  level : List Bool

theorem join_trace_inline_MachineRegularMetadata {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def querySteps (v x : Nat) : Nat := 2 * (x + 2) + 2 * (v + 2) + 1

def overhead (N x v : Nat) : Nat :=
  (2*x + 5*N + 6) + 2 + (N+1) + 2*(x+2) + 2*(v+2) + 1 +
    (5*N + 3*(v+x+2) + 6) + (v+x+3) + (N+1) + 2 + (v+2) + 2

theorem overhead_le (N x v : Nat) (hx : x ≤ N) (hv : v ≤ N) :
    overhead N x v ≤ 40*(N+1) := by
  unfold overhead
  omega

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

open Turing
open MachineCloudCount (Row rowWords rowsHits )

abbrev BaseState (σ : Type) := MachineCloudCount.State σ

inductive BaseLabel
  | queryFirst | querySecond | querySkip | tableFirst | tableSecond
  | headerFirst | headerSecond | field | restore | done | clearWork | clearRank
  | skip (i : Fin 4097)
  deriving DecidableEq, Fintype

def skipLabel (i : Nat) : BaseLabel :=
  if h : i < 4097 then .skip ⟨i, h⟩ else .done

variable {σ : Type}

inductive Phase | checking | advancing | finishing
  deriving DecidableEq

protected abbrev Phase.enumList : List Phase := [.checking, .advancing, .finishing]

protected theorem Phase.enumList_nodup : Phase.enumList.Nodup := by decide

instance instFintypePhase : Fintype Phase where
  elems := ⟨Phase.enumList, Phase.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive Control | initialize_ | dispatch
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize_, .dispatch]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Label := BaseLabel ⊕ Control
abbrev State (σ : Type) := BaseState σ × Phase

open MaxCutGames.Foundations.PCP

end MaxCutGames.Foundations.Complexity.MachineCloudSelect

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
open PCP.AlphabetTable

/-- One scaled scan/restore, one bounded offset, the delimiter, and final jump. -/
def emitSteps (n : Nat) : Nat := 3 * (n + 1) + 6

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

variable {K Λ ρ : Type} [DecidableEq K]

theorem join_trace_inline_MachineExpanderRowCleanup {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

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

/-!
# Complete execution of one expander-table row

The actual finite program performs both stored-table lookups, splits their
results by its fixed degree, emits the resulting square/zigzag reverse index,
and clears its work tapes. Its transition bound is linear in the unary input
table length. The output accumulator and finite caller state are arbitrary.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderRow

open Turing
open PCP.AlphabetTable

theorem concatenate_inline_MachineExpanderRow {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end MaxCutGames.Foundations.Complexity.MachineExpanderRow

/-!
# Concrete boundary steps of the expander-table machine

Every execution theorem below reduces the actual common program statement.
States and dependent tape frames are arbitrary; only the relevant unary word
or finite-position branch is specified. No phase execution is a premise.
-/

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

def singleStep_inline_MachineExpanderTableRows {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := Nat.le_refl _

def sequence_inline_MachineExpanderTableRows {α : Type*} {step : α → Option α} {a b c : α} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) := by
  simpa only [Nat.add_comm n m] using
    StateTransition.EvalsToInTime.trans step m n a b (some c) first second

def widen_inline_MachineExpanderTableRows {α : Type*} {step : α → Option α} {a : α} {b : Option α} {m n : Nat}
    (run : StateTransition.EvalsToInTime step a b m) (bound : m ≤ n) :
    StateTransition.EvalsToInTime step a b n where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bound

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

/-!
# Actual outer vertex iteration for expander tables

The invariant is the reversed unary encoding of all completed vertices. Each
positive unary guard invokes the proved complete fixed-position row loop;
the zero guard enters the actual output-reversal phase. No execution premise
is supplied by the caller.
-/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderTable

open Turing

def boundarySingleStep_inline_MachineExpanderTableLoop {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineExpanderTable

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

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineExpanderFamilyCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual counted repetition of complete table-expansion cycles. The input
counter is physically decremented, and the invariant carries the exact table
at the completed family level. -/

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing

def familySingleStep_inline_MachineExpanderFamilyLoop {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

namespace MaxCutGames.Foundations.Complexity.MachineExpanderFamily

open Turing

def singleFamilyStep_inline_MachineExpanderFamily {S : Type*} (f : S → Option S) (a b : S)
    (h : f a = some b) : StateTransition.EvalsToInTime f a (some b) 1 where
  steps := 1
  evals_in_steps := by change f a = some b; exact h
  steps_le_m := Nat.le_refl _

end MaxCutGames.Foundations.Complexity.MachineExpanderFamily

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

namespace MaxCutGames.Foundations.Complexity.MachineRegularFamily

open Turing
open MachineCloudPadding

theorem appendTrace_inline_MachineRegularFamily {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a+b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end MaxCutGames.Foundations.Complexity.MachineRegularFamily

/-! Physical comparison of two unary fields. Matched true bits are saved on
two empty scratch stacks. The first delimiter determines the comparison, then
both saved prefixes are restored. All input suffixes and other tapes survive. -/

namespace MaxCutGames.Foundations.Complexity.MachineUnaryLessAt

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

def stop (result : Bool) (restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .load (fun s => ((s.1.1, result), none)) (.goto fun _ => restoreLabel)

def scan (slots : Fin 4 ↪ K) (scanLabel restoreLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State σ) :=
  .peek (slots 0) (fun s head => (s.1, head))
    (.branch (fun s => s.2.getD false)
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (.pop (slots 0) (fun s _ => s)
            (.pop (slots 1) (fun s _ => s)
              (.push (slots 2) (fun _ => true)
                (.push (slots 3) (fun _ => true) (.goto fun _ => scanLabel)))))
          (stop false restoreLabel)))
      (.peek (slots 1) (fun s head => (s.1, head))
        (.branch (fun s => s.2.getD false)
          (stop true restoreLabel) (stop false restoreLabel))))

inductive Label where
  | scan
  | restoreLeft
  | restoreRight
  deriving DecidableEq

def steps (a b : Nat) : Nat := 3 * (min a b + 1)

end MaxCutGames.Foundations.Complexity.MachineUnaryLessAt

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_Alphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Physical construction of an internal regularization row

The input values belong on unary tapes. The cloud degree and the queried port
are the only arithmetic parameters fixed in finite control. The stored cloud
rotation supplies both the destination's local index and the return port.
The final row contains the full fixed equality predicate.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

open Turing
open PCP

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive FinishLabel
  | seedReturn | copyReturn | restoreReturn | affine | restoreTarget | equality
  | row (stage : MachineTableRows.Label)
  | clearReverse | clearEquality
  deriving DecidableEq, Fintype

/-- Tail, selected global target, returned port, scratch, reverse field,
equality field, row buffer, accumulated output. -/
def finishFields (tape : Fin 8 → K) : Fin 3 → K := fun i =>
  if i = 0 then tape 0 else if i = 1 then tape 4 else tape 5

omit [DecidableEq K] in
@[simp] theorem finishFields_zero (tape : Fin 8 → K) : finishFields tape 0 = tape 0 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_one (tape : Fin 8 → K) : finishFields tape 1 = tape 4 := rfl
omit [DecidableEq K] in
@[simp] theorem finishFields_two (tape : Fin 8 → K) : finishFields tape 2 = tape 5 := rfl

theorem joinTrace_inline_MachineRegularInternalRow {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def rotorLookupTapes (tape : Fin 8 → K) (j : Fin 5) : K :=
  tape ⟨j.val + 1, by omega⟩

omit [DecidableEq K] in
theorem rotorLookupTapes_injective (tape : Fin 8 → K) (h : Function.Injective tape) :
    Function.Injective (rotorLookupTapes tape) := by
  intro i j hij
  have hv := congrArg Fin.val (h hij)
  apply Fin.ext
  simpa only [Fin.val_mk, Nat.add_left_inj] using hv

omit [DecidableEq K] in
theorem rotorLookupTapes_outside (tape : Fin 8 → K) (h : Function.Injective tape)
    (i : Fin 5) : tape 0 ≠ rotorLookupTapes tape i := by
  intro he
  have hv := congrArg Fin.val (h he)
  change 0 = i.val + 1 at hv
  omega

inductive SelectExtraTape
  | localIndex | owner | cloudSize | prefixOffset | darts
  | savedLeft | savedRight | localWork | sizeWork
  deriving DecidableEq

abbrev SelectState (σ : Type) := MachineUnaryLessAt.State (σ × MachineCloudSelect.Phase)

def selectStateEquiv (σ : Type) : (MachineCloudSelect.State σ × Unit) ≃ SelectState σ where
  toFun s := (((s.1.1.1.1, s.1.2), s.1.1.1.2), s.1.1.2)
  invFun s := ((((s.1.1.1, s.1.2), s.2), s.1.1.2), ())
  left_inv s := by rcases s with ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, ⟨⟩⟩; rfl
  right_inv s := by rcases s with ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl

inductive SelectCopy
  | oldLocal | oldOwner | dummyLocal | dummySize | dummyDifference
  deriving DecidableEq

protected abbrev SelectCopy.enumList : List SelectCopy := [.oldLocal, .oldOwner, .dummyLocal,
  .dummySize, .dummyDifference]

protected theorem SelectCopy.enumList_nodup : SelectCopy.enumList.Nodup := by decide

instance instFintypeSelectCopy : Fintype SelectCopy where
  elems := ⟨SelectCopy.enumList, SelectCopy.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectAdd
  | prefixOffset | darts
  deriving DecidableEq

protected abbrev SelectAdd.enumList : List SelectAdd := [.prefixOffset, .darts]

protected theorem SelectAdd.enumList_nodup : SelectAdd.enumList.Nodup := by decide

instance instFintypeSelectAdd : Fintype SelectAdd where
  elems := ⟨SelectAdd.enumList, SelectAdd.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive SelectAddStage | scan | restore
  deriving DecidableEq

protected abbrev SelectAddStage.enumList : List SelectAddStage := [.scan, .restore]

protected theorem SelectAddStage.enumList_nodup : SelectAddStage.enumList.Nodup := by decide

instance instFintypeSelectAddStage : Fintype SelectAddStage where
  elems := ⟨SelectAddStage.enumList, SelectAddStage.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev CoreTape := Fin 27

def dummySelectSteps (j k o m : Nat) : Nat :=
  (2 * (j + 1) + 1) + (2 * (k + 1) + 1) + (k + 1) +
    (2 * (j - k + 1) + 1) + 2 * (o + 1) + 2 * (m + 1) + (j + k + 7)

theorem dummySelectSteps_eq (j k o m : Nat) (h : k ≤ j) :
    dummySelectSteps j k o m = 5 * j + 2 * k + 2 * o + 2 * m + 21 := by
  unfold dummySelectSteps
  omega

end MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_SelectorMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularInternalRow
open Turing
open PCP
variable {K Λ σ : Type} [DecidableEq K]

/-- The fixed core rotor roles use the agreed reusable 27-tape frame. -/
def coreRotorTapes : Fin 8 → CoreTape := ![3, 7, 10, 11, 12, 9, 13, 14]

/-- Tail, selected destination, return port, scratch and emitted row fields. -/
def coreFinishTapes : Fin 8 → CoreTape := ![1, 15, 14, 9, 24, 25, 26, 8]

def coreCleanupTape : Fin 10 → CoreTape := ![10, 11, 12, 13, 14, 15, 9, 16, 17, 18]

/-- For fixed cloud degree q this is affine in the lengths and unary values
on the actual input tapes. All relation/cleanup constants are included. -/
def coreTimeBound (q graphLength rotorLength x v i k o m outputLength : Nat) : Nat :=
  (5 * q + 32) * rotorLength + 10 * graphLength + 2 * i + 13 * v + 5 * k +
    (5 * q + 10) * (m + o) + 4 * x + 2 * outputLength + 8 * q + 41066

end MaxCutGames.Foundations.Complexity.MachineRegularInternalRow

/-!
# Reusable inherited-row execution with actual cleanup

Five concrete drain loops remove the query delimiter, unread scan suffix,
raw reverse field, computed reverse field, and copied relation. With initially
empty work tapes, the only final tape change is the appended output row. The
index on tape zero and input table on tape one are both preserved.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalClean

open Turing PCP

abbrev Tape := MachineRegularOriginalRow.Tape
abbrev Alphabet := MachineRegularOriginalRow.Alphabet

def cleanupTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update base 2 []) 3 []) 4 []) 6 []) 7 []

def cleanupSteps (base : Tape → List Bool) : Nat :=
  ((base 2).length + 1) + ((base 3).length + 1) + ((base 4).length + 1) +
    ((base 6).length + 1) + ((base 7).length + 1)

theorem join_trace_inline_MachineRegularOriginalClean {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def timeBound (q inputLength outputLength : Nat) : Nat :=
  (5 * q + 20) * inputLength + 2 * outputLength + 5 * q + 40995

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalClean

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

namespace MaxCutGames.Foundations.Complexity.MachineDummyRows

open Turing

/-- One initialization label and ten labels per fixed port. -/
abbrev Label (d : Nat) := Unit ⊕ (Fin d × (MachineTableRows.Label ⊕ Unit))

def start (d : Nat) : Label d := .inl ()
def rowLabel {d : Nat} (p : Fin d) (stage : MachineTableRows.Label) : Label d :=
  .inr (p, .inl stage)
def bumpLabel {d : Nat} (p : Fin d) : Label d := .inr (p, .inr ())

def fields : Fin 3 → Fin 6 := fun i => i.castLE (by decide)

/-- The only data-changing index operation is a tape push, below. This
function chooses a finite continuation among the fixed port-control labels. -/
def afterPort {d : Nat} (p : Fin d) : Option (Label d) :=
  if h : p.val + 1 < d then some (rowLabel ⟨p.val + 1, h⟩ .relationRead) else none

def entry (d : Nat) : Option (Label d) :=
  if h : 0 < d then some (rowLabel ⟨0, h⟩ .relationRead) else none

variable {σ : Type}

abbrev Alphabet (_ : Fin 6) := Bool

def continueAt {d : Nat} (exit : Option (Label d)) :
    TM2.Stmt Alphabet (Label d) (σ × Option Bool) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

theorem stepAux_continueAt {d : Nat} (exit : Option (Label d))
    (state : σ × Option Bool) (tapes : Fin 6 → List Bool) :
    TM2.stepAux (continueAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

end MaxCutGames.Foundations.Complexity.MachineDummyRows

/-!
# Actual inherited-row emission for a dummy vertex

The fixed program preserves the physical unary vertex index on tape zero,
computes its inherited reverse index on tape one, invokes the actual one-port
dummy-row emitter, and drains the computed index and fixed true relation.
Tape four accumulates output. Tapes one, two, three, and five are empty at both
boundaries. The degree is fixed program data, not an input-dependent control
parameter.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularDummyRow

open Turing

abbrev Tape := Fin 6
abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | affine (stage : MachineUnaryAffineAt.Label)
  | row (stage : MachineDummyRows.Label 1)
  | reverse | relation
  deriving DecidableEq, Fintype

def reverseIndex (q x : Nat) : Nat := (q + 1) * x + q

theorem join_trace_inline_MachineRegularDummyRow {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

/-- For each fixed degree, the exact cost is linear in index and prior output. -/
def timeBound (q x outputLength : Nat) : Nat :=
  (5 * q + 11) * x + 2 * outputLength + 5 * q + 40986

end MaxCutGames.Foundations.Complexity.MachineRegularDummyRow

namespace MaxCutGames.Foundations.Complexity.MachinePaddingRows

open Turing

inductive Control | initialize_ | guard | bump
  deriving DecidableEq

protected abbrev Control.enumList : List Control := [.initialize_, .guard, .bump]

protected theorem Control.enumList_nodup : Control.enumList.Nodup := by decide

instance instFintypeControl : Fintype Control where
  elems := ⟨Control.enumList, Control.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 6 ⊕ Unit
abbrev Label (d : Nat) := MachineDummyRows.Label d ⊕ Control
abbrev State := (Unit × Option Bool) × Unit

def bodyEntry (d : Nat) (hd : 0 < d) : Label d :=
  .inl (MachineDummyRows.rowLabel ⟨0, hd⟩ .relationRead)

end MaxCutGames.Foundations.Complexity.MachinePaddingRows

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

open Turing PCP MachineRegularInternalRow

variable {σ Λ : Type}

/-- A prefix of the emitted rows, defined without any execution hypothesis. -/
def portBits {q : Nat} (bits : Fin q → List Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => portBits bits k ++ if h : k < q then bits ⟨k, h⟩ else []

theorem joinTrace_inline_MachineRegularVertexBlock {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

/-- Uniform bound on a serialized row in the actual output table. -/
def rowSizeBound (q vertices : Nat) : Nat := vertices + vertices * (q + 1) + 8192

theorem portBits_length_le {q : Nat} (bits : Fin q → List Bool) (bound : Nat)
    (hbits : ∀ p, (bits p).length ≤ bound) (k : Nat) :
    (portBits bits k).length ≤ k * bound := by
  induction k with
  | zero => simp only [portBits, List.length_nil, Nat.zero_mul, le_refl]
  | succ k ih =>
    rw [portBits, List.length_append]
    split_ifs with h
    · have hp := hbits ⟨k, h⟩
      rw [Nat.succ_mul]
      exact Nat.add_le_add ih hp
    · simp only [List.length_nil, Nat.add_zero]
      exact ih.trans (Nat.mul_le_mul_right bound (by omega))

def portTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  q * coreTimeBound q graphLength rotorLength x v i k o m
    (outputLength + q * rowSizeBound q vertices)

def originalTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularOriginalClean.timeBound q graphLength
      (outputLength + q * rowSizeBound q vertices)

def dummyTimeBound (q graphLength rotorLength x v i k o m outputLength vertices : Nat) : Nat :=
  portTimeBound q graphLength rotorLength x v i k o m outputLength vertices +
    MachineRegularDummyRow.timeBound q x (outputLength + q * rowSizeBound q vertices)

end MaxCutGames.Foundations.Complexity.MachineRegularVertexBlock

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOriginalBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# One actual original-vertex body of regularization

The finite code composes physical metadata preparation, expander-family
materialization, all vertex rows, and seven metadata drain loops. The outer
loop owns the global vertex counter and keeps it unchanged during this body.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

open Turing PCP
abbrev MetaState := MachineRegularMetadata.State Unit

theorem joinTrace_inline_MachineRegularOriginalBody {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBody

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup

open Turing

variable {Λ : Type}

/-- Constructor-by-constructor equality for a fixed sum of tape alphabets. -/
def sumDecidableEq_inline_MachineRegularOwnerCleanup {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup

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

/-- Bits emitted by the first `k` blocks. -/
def blocksPrefix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).take k).flatten

/-- Bits remaining after the first `k` blocks. -/
def blocksSuffix {n : Nat} (f : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn f).drop k).flatten

@[simp] theorem blocksPrefix_zero {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f 0 = [] := by
  simp only [blocksPrefix, List.take_zero, List.flatten_nil]

@[simp] theorem blocksPrefix_all {n : Nat} (f : Fin n → List Bool) :
    blocksPrefix f n = (List.ofFn f).flatten := by
  have h : (List.ofFn f).take n = List.ofFn f := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn f))
  exact congrArg List.flatten h

theorem blocksPrefix_succ {n : Nat} (f : Fin n → List Bool) (k : Nat) (h : k < n) :
    blocksPrefix f (k + 1) = blocksPrefix f k ++ f ⟨k, h⟩ := by
  unfold blocksPrefix
  rw [List.take_succ_eq_append_getElem
    (show k < (List.ofFn f).length by simpa only [List.length_ofFn] using h)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.getElem_ofFn]

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

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing PCP
open PreprocessingRegularLoopWords

abbrev MetaState := MachineRegularOriginalBody.MetaState

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing PCP
open PreprocessingRegularLoopWords

theorem joinTrace_inline_MachineRegularOwnerBody {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingMachineBounds
open MaxCutGames.Foundations.Complexity
open scoped BigOperators

/-- A two-parameter bound for the complete unary graph codec. -/
noncomputable def tablePolynomial (a b : Nat) : Polynomial Nat :=
  Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 2 +
    (Polynomial.C b * Polynomial.X) *
      (Polynomial.C a * Polynomial.X + Polynomial.C b * Polynomial.X + 8192)

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

open Turing
open MaxCutGames.Foundations.PCP

namespace Header

inductive Extra
  | m | index | work | scratch | vertices | darts | emit | output
  deriving DecidableEq

protected abbrev Extra.enumList : List Extra := [.m, .index, .work, .scratch, .vertices,
  .darts, .emit, .output]

protected theorem Extra.enumList_nodup : Extra.enumList.Nodup := by decide

abbrev State (σ : Type) := MachineCloudPrefix.State σ

inductive Field
  | vertices | darts
  deriving DecidableEq

protected abbrev Field.enumList : List Field := [.vertices, .darts]

protected theorem Field.enumList_nodup : Field.enumList.Nodup := by decide

instance instFintypeField : Fintype Field where
  elems := ⟨Field.enumList, Field.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive CopyPhase
  | count | rEmit | nEmit
  deriving DecidableEq

protected abbrev CopyPhase.enumList : List CopyPhase := [.count, .rEmit, .nEmit]

protected theorem CopyPhase.enumList_nodup : CopyPhase.enumList.Nodup := by decide

instance instFintypeCopyPhase : Fintype CopyPhase where
  elems := ⟨CopyPhase.enumList, CopyPhase.enumList_nodup⟩
  complete x := by cases x <;> decide

variable {σ : Type}

theorem appendTrace_inline_MachineRegularTable {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

end Header

namespace Fuel

variable {K Λ σ : Type} [DecidableEq K]

/-- The outer loop consumes one real unary fuel bit. The zero delimiter is
consumed on exit; its temporary finite register is reset on both branches. -/
def guard (fuel : K) (body : Λ) (exit : Option Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool) :=
  .pop fuel (fun s bit => (s.1, bit))
    (.branch (fun s => s.2.getD false)
      (.load (fun s => (s.1, none)) (.goto fun _ => body))
      (.load (fun s => (s.1, none))
        (match exit with | some label => .goto fun _ => label | none => .halt)))

/-- Unary successor needs one physical push and no unbounded register. -/
def increment (counter : K) (next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ σ :=
  .push counter (fun _ => true) (.goto fun _ => next)

end Fuel

namespace Top

def sumDecidableEq_inline_MachineRegularTable {A B : Type} (left : DecidableEq A) (right : DecidableEq B) :
    DecidableEq (A ⊕ B)
  | .inl a, .inl b => match left a b with
      | .isTrue h => .isTrue (congrArg (Sum.inl : A → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match right a b with
      | .isTrue h => .isTrue (congrArg (Sum.inr : B → A ⊕ B) h)
      | .isFalse h => .isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => .isFalse (by intro h; cases h)
  | .inr _, .inl _ => .isFalse (by intro h; cases h)

end Top
end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_InputData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable
open Turing
open MaxCutGames.Foundations.PCP

namespace Top

def counterStacks (old owners dummy work : List Bool) : Fin 4 → List Bool :=
  ![old, owners, dummy, work]

end Top

end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_CloneMachineModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Affine word emission in the actual clone-table machine

The shared machine keeps its context fixed while copying one saved word. Its
finite transducer therefore acts by a fixed symbol substitution. The lemmas
below identify that substitution with the established unary encoding of
`offset + scale * value`, including all header and equation-field contexts.
Scale, offset, and the triple-table length remain symbolic.
-/

namespace MaxCutGames.Reduction.MachineAddressHeaders

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

namespace Prefix

variable {K Λ σ : Type} [DecidableEq K]

def copied (slots : Fin 5 ↪ K) (base : K → List Bool) : K → List Bool :=
  Function.update base (slots 1) (base (slots 0))

end Prefix

noncomputable section

namespace Arithmetic

variable {k s d noiseCount : Nat} {K Λ σ : Type}

variable [DecidableEq K]

theorem trace_trans_inline_MachineAddressHeaders {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end Arithmetic

end

end MaxCutGames.Reduction.MachineAddressHeaders

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

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

theorem replicate_append_cons_inline_MachineInitialHeaders (n : ℕ) (xs : List Bool) :
    List.replicate n true ++ true :: xs = List.replicate (n + 1) true ++ xs := by
  rw [List.replicate_add]
  simp

theorem trace_trans_inline_MachineInitialHeaders {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MaxCutGames.Foundations.Complexity.MachineInitialHeaders

/-! A finite literal setup sequence. Its list is fixed with the machine; no
input word or unbounded address is stored in finite control. -/

namespace MaxCutGames.Explicit.MachineProductSeed

open Turing
open MaxCutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K]

abbrev Command (K : Type) := K × List Bool
abbrev LocalLabel (_ : Command K) := Unit

def result (command : Command K) (base : K → List Bool) : K → List Bool :=
  Function.update base command.1 (command.2 ++ base command.1)

end MaxCutGames.Explicit.MachineProductSeed

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineTemplateAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed canonical-word template followed by actual radix-address execution.
The program is determined by the fixed tokens and tape layout. Numeric field
values enter only the tape invariants and execution theorem, never the labels. -/

namespace MaxCutGames.Reduction.MachineTemplateAddress

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

variable {q width : Nat} {K Λ σ : Type} [DecidableEq K]

def digits (values : List Nat) (i : Nat) : Nat := values[i]?.getD 0

end MaxCutGames.Reduction.MachineTemplateAddress

/-! Actual edge emission from two fixed address templates. Capacity is copied
before unary addition, so the original capacity tape is preserved. All local
labels and literal instructions depend only on fixed templates and layout. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_EquationLookup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.SourceEquationLookup

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open SourceMachine

variable {σ : Type}

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (L : Nat) : timePolynomial.eval L = 4 * L + 8 := by
  simp [timePolynomial]

end MaxCutGames.Reduction.SourceEquationLookup

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AddressOdometerSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.AddressOdometerSchedule

open Turing
open MaxCutGames.Foundations.Complexity MachineTupleOdometer
open MaxCutGames.Foundations.Hastad

noncomputable section

variable {k s d noiseCount m : ℕ} {Λ σ : Type}

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

end
end MaxCutGames.Reduction.AddressOdometerSchedule

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

open Turing

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

inductive Label (d : Nat)
  | copySeed | copyScan | copyRestore | initialize_ | divide
  | emit (r : Fin d)
  | affineScan | affineRestore | drainQuotient | finish
  deriving DecidableEq, Fintype

def steps (d j : Nat) : Nat := 3 * j + 3 * (j / d) + 11

def value (d c b j : Nat) : Nat := c * (j / d) + (j % d) + b

theorem joinTrace_inline_MachinePortReindex {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem lazy_value (d j : Nat) : value d (2 * d) d j =
    2 * d * (j / d) + d + (j % d) := by
  unfold value
  omega

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

open MaxCutGames.Foundations.Complexity

variable {n d : Nat}

/-- The machine's fixed-degree numerical map for an old reverse-row index. -/
def reverseMap (d j : Nat) : Nat := 2 * d * (j / d) + d + j % d

end MaxCutGames.Foundations.PCP.PreprocessingLazyWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineLazyRows

open Turing
open PCP.PreprocessingLazyWords (reverseMap )

variable {K Λ A : Type} [DecidableEq K]

abbrev Label (d : Nat) := MachinePortReindex.Label d ⊕ MachineTableRows.Label

/-- Tape roles: tail, old reverse, relation, scratch, divided copy,
quotient, new reverse, accumulated output, row buffer. -/
def addressIndex : Fin 5 → Fin 9 := ![1, 3, 4, 5, 6]

theorem addressIndex_injective : Function.Injective addressIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [addressIndex]

def fields (tape : Fin 9 → K) : Fin 3 → K := ![tape 0, tape 6, tape 2]

def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 10 => k.val) h

inductive StreamLabel (d : Nat)
  | tailStart | tailRead | reverseStart | reverseRead | copyRelation
  | row (stage : Label d)
  | clearTail | clearOld | clearRelation | clearNew
  deriving DecidableEq, Fintype

theorem joinTrace_inline_MachineLazyRows {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

abbrev VertexLabel (d : Nat) := Fin (d + 1) × Option (StreamLabel d)

def valueBound (c b m : Nat) : Nat := c * m + m + b
def rowSizeBound (c b n m : Nat) : Nat := n + valueBound c b m + 8194
def rowCostBound (c b n m : Nat) : Nat :=
  2 * n + 8 * m + valueBound c b m + 4 * rowSizeBound c b n m + 8224

end MaxCutGames.Foundations.Complexity.MachineLazyRows

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

open Complexity

variable {n d e : Nat}

def oldReverseMap (d e j : Nat) : Nat := (d + e) * (j / d) + j % d
def expanderReverseMap (d e j : Nat) : Nat := (d + e) * (j / e) + d + j % e

end MaxCutGames.Foundations.PCP.PreprocessingOverlayWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineOverlayRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineOverlayRows

open Turing
open PCP.PreprocessingOverlayWords

variable {K Λ A : Type} [DecidableEq K]

inductive Label (e : Nat)
  | loadStart | loadLoop | seedRelation
  | row (stage : MachineLazyRows.Label e)
  | drainOld | drainNew | drainRelation
  deriving DecidableEq, Fintype

/-- The row body's nine tapes retain their numbering; tape 9 is the stream. -/
def bodyIndex (i : Fin 9) : Fin 10 := i.castSucc

theorem bodyIndex_injective : Function.Injective bodyIndex := by
  intro i j h
  exact Fin.castSucc_injective 9 h

theorem joinTrace_inline_MachineOverlayRows {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

/-! The fixed-degree vertex loop has one finite label block per port, plus
one terminal boundary. The stored row values do not occur in its program. -/

abbrev VertexLabel (e : Nat) := Fin (e + 1) × Option (Label e)

def valueBound (d e B : Nat) : Nat := (d + e) * B + B + d

theorem value_le (d e j B : Nat) (hj : j ≤ B) :
    MachinePortReindex.value e (d + e) d j ≤ valueBound d e B := by
  have hdiv := (Nat.div_le_self j e).trans hj
  have hmod := (Nat.mod_le j e).trans hj
  have hmul := Nat.mul_le_mul_left (d + e) hdiv
  unfold MachinePortReindex.value valueBound
  omega

end MaxCutGames.Foundations.Complexity.MachineOverlayRows

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

open Turing

/-- The homogeneous parts of a finite machine, without dependent alphabet casts. -/
structure Program (K Λ σ : Type) where
  input : K
  output : K
  main : Λ
  initial : σ
  code : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ

section Structural

variable {K Λ Λ' σ : Type} [DecidableEq K]

def extendedLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def extendedCfg (labels : Λ → Λ') (haltTarget : Option Λ') (register : Option Bool)
    (cfg : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ' (σ × Option Bool) :=
  ⟨extendedLabel labels haltTarget cfg.l, (cfg.var, register), cfg.stk⟩

/-- Add one finite scratch register while preserving each raw transition. -/
def extendedStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt (fun _ : K => Bool) Λ σ →
      TM2.Stmt (fun _ : K => Bool) Λ' (σ × Option Bool)
  | .push k f next => .push k (fun state => f state.1)
      (extendedStmt labels haltTarget next)
  | .peek k f next => .peek k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .pop k f next => .pop k (fun state symbol => (f state.1 symbol, state.2))
      (extendedStmt labels haltTarget next)
  | .load f next => .load (fun state => (f state.1, state.2))
      (extendedStmt labels haltTarget next)
  | .branch test yes no => .branch (fun state => test state.1)
      (extendedStmt labels haltTarget yes) (extendedStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state.1))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_extended (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ)
    (register : Option Bool) (tapes : K → List Bool) :
    TM2.stepAux (extendedStmt labels haltTarget stmt) (state, register) tapes =
      extendedCfg labels haltTarget register (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true =>
          simpa only [extendedStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Structural

variable {K Λ σ : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype σ]

def sourceMachine (P : Program K Λ σ) : FinTM2 where
  K := K
  k₀ := P.input
  k₁ := P.output
  Γ _ := Bool
  Λ := Λ
  main := P.main
  σ := σ
  initialState := P.initial
  m := P.code

end MaxCutGames.Foundations.Complexity.MachineCanonicalOutput

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

open Turing PCP
open PreprocessingMachineBounds MachineRegularOriginalBody

theorem originalTimeBound_le (q L R x v i k o m O V W R' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ W) (hV : V ≤ W) :
    MachineRegularVertexBlock.originalTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.originalTimeBound q W R' W W W W W W W W := by
  unfold MachineRegularVertexBlock.originalTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularOriginalClean.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

end MaxCutGames.Foundations.Complexity.MachineRegularOriginalBodyBounds

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing PCP
open PreprocessingMachineBounds PreprocessingRegularLoopWords

theorem dummyTimeBound_le (q L R x v i k o m O V W R' O' : Nat)
    (hL : L ≤ W) (hR : R ≤ R') (hx : x ≤ W) (hv : v ≤ W)
    (hi : i ≤ W) (hk : k ≤ W) (ho : o ≤ W) (hm : m ≤ W)
    (hO : O ≤ O') (hV : V ≤ W) :
    MachineRegularVertexBlock.dummyTimeBound q L R x v i k o m O V ≤
      MachineRegularVertexBlock.dummyTimeBound q W R' W W W W W W O' W := by
  unfold MachineRegularVertexBlock.dummyTimeBound MachineRegularVertexBlock.portTimeBound
    MachineRegularInternalRow.coreTimeBound MachineRegularDummyRow.timeBound
    MachineRegularVertexBlock.rowSizeBound
  gcongr

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

namespace MaxCutGames.Foundations.Complexity.MachineTableSplit

open Turing

abbrev State (σ : Type) := σ × Option Bool

inductive Label
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.copyFirst, .copySecond, .startVertices,
  .readVertices, .startDarts, .readDarts]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

noncomputable def timePolynomial : Polynomial Nat := Polynomial.C 4 * Polynomial.X + Polynomial.C 6

@[simp] theorem timePolynomial_eval (length : Nat) :
    timePolynomial.eval length = 4 * length + 6 := by simp [timePolynomial]

end MaxCutGames.Foundations.Complexity.MachineTableSplit

/-! Polynomial bounds for the actual outer padding-loop recurrence. No
execution or cost premise is introduced: the recurrence is the one matched
to the concrete machine by `MachinePaddingRows.loopTrace`. -/

namespace MaxCutGames.Foundations.Complexity.MachinePaddingBounds

/-- A common row-size bound for all remaining vertices and ports. -/
def rowBound (d v e count : Nat) : Nat := v + count + e + (count + 1) * d + 8194

/-- This bound is invariant when one vertex and its `d` reverse indices
have been consumed from the remaining outer-loop count. -/
theorem rowBound_next (d v e count : Nat) :
    rowBound d (v + 1) (e + d) count = rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

theorem blockRow_le_rowBound (d v e count : Nat) :
    v + e + d + 8194 ≤ rowBound d v e (count + 1) := by
  simp only [rowBound, Nat.add_mul, Nat.one_mul]
  omega

def rowCap (d size : Nat) : Nat := size + (size + 1) * d + 8194

noncomputable def rowPolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + 1) * Polynomial.C d + Polynomial.C 8194

/-- A cubic polynomial for fixed degree, including the final zero-fuel
guard. The one-time relation initializer can be accounted for separately. -/
noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C d *
    (Polynomial.C 4 * rowPolynomial d +
      Polynomial.C 2 * (Polynomial.X + Polynomial.X * Polynomial.C d * rowPolynomial d) +
      Polynomial.C 10) + Polynomial.C 2) + 1

end MaxCutGames.Foundations.Complexity.MachinePaddingBounds

/-! Polynomial-time certificate for the actual varying-length padding loop,
including its one-time relation initialization. The input vertex, reverse
index, fuel, and accumulated output are all measured as physically stored
bits. This is a reusable stage of the graph-table transformation. -/

namespace MaxCutGames.Foundations.Complexity.MachinePaddingCertificate

open MachinePaddingRows

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  MachinePaddingBounds.timePolynomial d + 1

end MaxCutGames.Foundations.Complexity.MachinePaddingCertificate

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

open Turing
open MaxCutGames.Foundations.PCP
open MachineCloudPadding

inductive Tape
  | original | output | vertex | edge | power | level | fuel | relation
  | scratch | work | saved | product | rowWork | rowSpare
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.original, .output, .vertex, .edge, .power,
  .level, .fuel, .relation, .scratch, .work, .saved, .product, .rowWork, .rowSpare]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Tape) := Bool
abbrev State (σ : Type) := (σ × Bool) × Option Bool

/-- All unnamed work stacks are empty at the phase boundaries below. -/
def memory (input output vertex edge power level fuel relation : List Bool) : Tape → List Bool
  | .original => input
  | .output => output
  | .vertex => vertex
  | .edge => edge
  | .power => power
  | .level => level
  | .fuel => fuel
  | .relation => relation
  | _ => []

@[simp] theorem update_output (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .output x = memory a x c d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_vertex (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .vertex x = memory a b x d e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_edge (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .edge x = memory a b c x e f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_power (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .power x = memory a b c d x f g h := by
  funext k; cases k <;> rfl
@[simp] theorem update_fuel (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .fuel x = memory a b c d e f x h := by
  funext k; cases k <;> rfl
@[simp] theorem update_relation (a b c d e f g h x : List Bool) :
    Function.update (memory a b c d e f g h) .relation x = memory a b c d e f g x := by
  funext k; cases k <;> rfl

def rowTape : MachinePaddingRows.Tape → Tape
  | .inl k => (![.vertex, .edge, .relation, .rowWork, .output, .rowSpare] : Fin 6 → Tape) k
  | .inr _ => .fuel
def rowView : Tape → Option MachinePaddingRows.Tape
  | .vertex => some (.inl 0)
  | .edge => some (.inl 1)
  | .relation => some (.inl 2)
  | .rowWork => some (.inl 3)
  | .output => some (.inl 4)
  | .rowSpare => some (.inl 5)
  | .fuel => some (.inr ())
  | _ => none

theorem rowView_left (k : MachinePaddingRows.Tape) : rowView (rowTape k) = some k := by
  rcases k with k | k
  · fin_cases k <;> rfl
  · cases k; rfl
theorem rowView_right (j : Tape) (k : MachinePaddingRows.Tape)
    (h : rowView j = some k) : rowTape k = j := by
  rcases k with k | k
  · cases j <;> fin_cases k <;> simp_all [rowView, rowTape]
  · cases k; cases j <;> simp_all [rowView, rowTape]

def rowStateEquiv (σ : Type) : (MachinePaddingRows.State × (σ × Bool)) ≃ State σ where
  toFun x := (x.2, x.1.1.2)
  invFun x := ((((), x.2), ()), x.1)
  left_inv := by rintro ⟨⟨⟨⟨⟩, r⟩, ⟨⟩⟩, a⟩; rfl
  right_inv := by rintro ⟨a, r⟩; rfl

theorem appendTrace_inline_MachineVertexPadding {α : Type} (f : α → α) {a b : Nat} {x y z : α}
    (hs : f^[a] x = y) (ht : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm a b, Function.iterate_add_apply, hs, ht]

def cleanupTime (d m : Nat) : Nat := 2 * m + m * d + 8201

end MaxCutGames.Foundations.Complexity.MachineVertexPadding

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineOverlayTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineOverlayTable

open Turing
open PCP PCP.PreprocessingOverlayWords
open MachineCloudPadding

variable {A : Type} {d e : Nat}

abbrev Tape := Fin 5 ⊕ Fin 12

def graphArchive : Tape := .inl 0
def graphStream : Tape := .inl 1
def scratch : Tape := .inl 2
def vertexCount : Tape := .inl 3
def dartCount : Tape := .inl 4
def expanderArchive : Tape := .inr 0
def expanderStream : Tape := .inr 1
def fuel : Tape := .inr 2
def vertex : Tape := .inr 3
def tail : Tape := .inr 4
def oldReverse : Tape := .inr 5
def relation : Tape := .inr 6
def dividedCopy : Tape := .inr 7
def quotient : Tape := .inr 8
def newReverse : Tape := .inr 9
def rowBuffer : Tape := .inr 10
def output : Tape := .inr 11

def oldTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, graphStream]

def expanderTapes : Fin 10 → Tape :=
  ![tail, oldReverse, relation, scratch, dividedCopy, quotient, newReverse,
    output, rowBuffer, expanderStream]

theorem oldTapes_injective : Function.Injective oldTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [oldTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, graphStream]

theorem expanderTapes_injective : Function.Injective expanderTapes := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [expanderTapes, tail, oldReverse, relation, scratch, dividedCopy, quotient,
      newReverse, output, rowBuffer, expanderStream]

inductive MainLabel (d e : Nat)
  | copyHFirst | copyHSecond
  | countSeed | countScan | countRestore
  | headerSeed | headerScan | headerRestore
  | fuelSeed | fuelScan | fuelRestore | vertexSeed | guard
  | old (stage : MachineLazyRows.VertexLabel d)
  | tailSeed | tailScan | tailRestore
  | expander (stage : MachineOverlayRows.VertexLabel e)
  | drainTail | increment
  | drainFuel | drainVertex | drainVertexCount | drainDartCount
  deriving DecidableEq, Fintype

abbrev Label (d e : Nat) := MachineTableSplit.Label ⊕ MainLabel d e

def next (l : MainLabel d e) : Option (Label d e) := some (.inr l)

def extraTapes (rawH : List Bool) : Fin 12 → List Bool :=
  fun i => if i = 0 then rawH else []

def splitView : Tape → Option (Fin 5)
  | .inl i => some i
  | .inr _ => none

def combine (left : Fin 5 → List Bool) (rawH : List Bool) : Tape → List Bool
  | .inl i => left i
  | .inr i => extraTapes rawH i

/-- Every unnamed work tape is empty at these phase boundaries. -/
def memory (g h gs hs n m f v t out : List Bool) : Tape → List Bool
  | .inl i => ![g, gs, [], n, m] i
  | .inr i => ![h, hs, f, v, t, [], [], [], [], [], [], out] i

@[simp] theorem memory_graphArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphArchive = g := rfl
@[simp] theorem memory_graphStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out graphStream = gs := rfl
@[simp] theorem memory_scratch (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out scratch = [] := rfl
@[simp] theorem memory_vertexCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertexCount = n := rfl
@[simp] theorem memory_dartCount (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dartCount = m := rfl
@[simp] theorem memory_expanderArchive (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderArchive = h := rfl
@[simp] theorem memory_expanderStream (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out expanderStream = hs := rfl
@[simp] theorem memory_fuel (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out fuel = f := rfl
@[simp] theorem memory_vertex (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out vertex = v := rfl
@[simp] theorem memory_tail (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out tail = t := rfl
@[simp] theorem memory_oldReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out oldReverse = [] := rfl
@[simp] theorem memory_relation (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out relation = [] := rfl
@[simp] theorem memory_dividedCopy (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out dividedCopy = [] := rfl
@[simp] theorem memory_quotient (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out quotient = [] := rfl
@[simp] theorem memory_newReverse (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out newReverse = [] := rfl
@[simp] theorem memory_rowBuffer (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out rowBuffer = [] := rfl
@[simp] theorem memory_output (g h gs hs n m f v t out : List Bool) :
    memory g h gs hs n m f v t out output = out := rfl

@[simp] theorem update_output (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) output x = memory g h gs hs n m f v t x := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_expanderStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) expanderStream x =
      memory g h gs x n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_graphStream (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) graphStream x =
      memory g h x hs n m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_fuel (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) fuel x = memory g h gs hs n m x v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertex (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertex x = memory g h gs hs n m f x t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_tail (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) tail x = memory g h gs hs n m f v x out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_vertexCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) vertexCount x = memory g h gs hs x m f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl
@[simp] theorem update_dartCount (g h gs hs n m f v t out x : List Bool) :
    Function.update (memory g h gs hs n m f v t out) dartCount x = memory g h gs hs n x f v t out := by
  funext k; rcases k with i | i <;> fin_cases i <;> rfl

theorem joinTrace_inline_MachineOverlayTable {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def preparationSteps (n : Nat) (h : List Bool) : Nat := 2 * (h.length + 1) + 6 * (n + 1) + 4

def remaining {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).drop k).flatten
def emittedPrefix {n : Nat} (block : Fin n → List Bool) (k : Nat) : List Bool :=
  ((List.ofFn block).take k).flatten

theorem remaining_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    remaining block v.val = block v ++ remaining block (v.val + 1) := by
  have hs := List.getElem_cons_drop (as := List.ofFn block) (i := v.val)
    (by simpa only [List.length_ofFn] using v.isLt)
  unfold remaining
  rw [← hs]
  simp only [List.flatten_cons, List.getElem_ofFn, Fin.eta]

theorem prefix_step {n : Nat} (block : Fin n → List Bool) (v : Fin n) :
    emittedPrefix block (v.val + 1) = emittedPrefix block v.val ++ block v := by
  unfold emittedPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_ofFn] using v.isLt)]
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.getElem_ofFn, Fin.eta]

@[simp] theorem remaining_zero {n : Nat} (block : Fin n → List Bool) :
    remaining block 0 = (List.ofFn block).flatten := by simp [remaining]
@[simp] theorem remaining_end {n : Nat} (block : Fin n → List Bool) :
    remaining block n = [] := by
  unfold remaining
  rw [List.drop_eq_nil_iff.mpr (by simpa only [List.length_ofFn] using (Nat.le_refl n)), List.flatten_nil]
@[simp] theorem prefix_zero {n : Nat} (block : Fin n → List Bool) : emittedPrefix block 0 = [] := by
  simp [emittedPrefix]
@[simp] theorem prefix_end {n : Nat} (block : Fin n → List Bool) :
    emittedPrefix block n = (List.ofFn block).flatten := by
  unfold emittedPrefix
  have ht : (List.ofFn block).take n = List.ofFn block :=
    List.take_of_length_le (by simpa only [List.length_ofFn] using (Nat.le_refl n))
  rw [ht]

def cleanupSteps (n m : Nat) : Nat := 2 * n + m + 8

theorem flatMap_length_le_inline_MachineOverlayTable {α : Type*} (items : List α) (f : α → List Bool)
    (B : Nat) (bounded : ∀ x ∈ items, (f x).length ≤ B) :
    (items.flatMap f).length ≤ items.length * B := by
  induction items with
  | nil => simp
  | cons x xs ih =>
      have hx := bounded x (by simp)
      have ht := ih (fun y hy => bounded y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

theorem flatten_length_le_inline_MachineOverlayTable (items : List (List Bool)) (B : Nat)
    (bounded : ∀ x ∈ items, x.length ≤ B) : items.flatten.length ≤ items.length * B := by
  simpa only [List.flatMap_id] using flatMap_length_le_inline_MachineOverlayTable items id B bounded

def oldSize (d e n : Nat) : Nat := MachineLazyRows.rowSizeBound (d + e) 0 n (n * d)

end MaxCutGames.Foundations.Complexity.MachineOverlayTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineLazyTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual whole-table lazy-graph machine, with fixed positive old degree.
All unbounded counts and addresses reside on unary tapes. -/

namespace MaxCutGames.Foundations.Complexity.MachineLazyTable

open Turing PCP

inductive Tape
  | input | output | source | vertices | darts | fuel | vertex | reverse
  | tail | old | relation | scratch | divided | quotient | newReverse | rowBuffer
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .source, .vertices, .darts,
  .fuel, .vertex, .reverse, .tail, .old, .relation, .scratch, .divided, .quotient,
  .newReverse, .rowBuffer]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def splitRoles : Fin 5 → Tape := ![.input, .source, .scratch, .vertices, .darts]
def splitView : Tape → Option (Fin 5)
  | .input => some 0 | .source => some 1 | .scratch => some 2
  | .vertices => some 3 | .darts => some 4 | _ => none

def dummyRoles : Fin 6 → Tape := ![.tail, .reverse, .relation, .rowBuffer, .output, .scratch]
def dummyView : Tape → Option (Fin 6)
  | .tail => some 0 | .reverse => some 1 | .relation => some 2
  | .rowBuffer => some 3 | .output => some 4 | .scratch => some 5 | _ => none

def oldRoles : Fin 10 → Tape :=
  ![.tail, .old, .relation, .scratch, .divided, .quotient, .newReverse,
    .output, .rowBuffer, .source]

theorem splitRoles_left (i : Fin 5) : splitView (splitRoles i) = some i := by
  fin_cases i <;> rfl

theorem splitRoles_right (t : Tape) (i : Fin 5) (h : splitView t = some i) : splitRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [splitView, splitRoles]

theorem dummyRoles_left (i : Fin 6) : dummyView (dummyRoles i) = some i := by
  fin_cases i <;> rfl

theorem dummyRoles_right (t : Tape) (i : Fin 6) (h : dummyView t = some i) : dummyRoles i = t := by
  cases t <;> fin_cases i <;> simp_all [dummyView, dummyRoles]

theorem oldRoles_injective : Function.Injective oldRoles := by decide

inductive Label (d : Nat)
  | split (label : MachineTableSplit.Label)
  | dartSeed | dartScan | dartRestore | vertexSeed | vertexScan | vertexRestore
  | fuelFirst | fuelSecond | seedCounters | guard | copyVertexFirst | copyVertexSecond
  | dummy (label : MachineDummyRows.Label d)
  | clearDummyTail | clearDummyRelation
  | oldRows (label : MachineLazyRows.VertexLabel d)
  | nextVertex | clearVertices | clearDarts | clearFuel | clearVertex | clearReverse
  deriving DecidableEq, Fintype

def frame (input source output vertices darts fuel vertex reverse : List Bool) : Tape → List Bool
  | .input => input | .source => source | .output => output
  | .vertices => vertices | .darts => darts | .fuel => fuel
  | .vertex => vertex | .reverse => reverse | _ => []

def initialTapes (input : List Bool) : Tape → List Bool := frame input [] [] [] [] [] [] []

def finalTapes (input output : List Bool) : Tape → List Bool := frame input [] output [] [] [] [] []

theorem joinTrace_inline_MachineLazyTable {X : Type} {f : X → X} {a b c : X} {s t : Nat}
    (first : f^[s] a = b) (second : f^[t] b = c) : f^[s + t] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem frame_old_empty (input source output vertices darts fuel vertex reverse : List Bool)
    (i : Fin 10) (h7 : i ≠ 7) (h9 : i ≠ 9) :
    frame input source output vertices darts fuel vertex reverse (oldRoles i) = [] := by
  fin_cases i <;> simp_all [frame, oldRoles]

def finishSteps (d n m v : Nat) : Nat := n + m + v + 2 * d * v + 11

def remaining (n r : Nat) : List (Fin n) := (List.finRange n).drop r

@[simp] theorem remaining_zero (n : Nat) : remaining n 0 = List.finRange n := by simp [remaining]
@[simp] theorem remaining_done (n : Nat) : remaining n n = [] := by simp [remaining]

theorem remaining_cons (n r : Nat) (h : r < n) :
    remaining n r = ⟨r, h⟩ :: remaining n (r + 1) := by
  unfold remaining
  rw [List.drop_eq_getElem_cons (l := List.finRange n) (i := r) (by simpa using h)]
  simp

noncomputable def timePolynomial (d : Nat) : Polynomial Nat :=
  Polynomial.C (1000000 * (d + 1) ^ 3 + 100) * (Polynomial.X + 1) ^ 3

@[simp] theorem timePolynomial_eval (d L : Nat) :
    (timePolynomial d).eval L = (1000000 * (d + 1) ^ 3 + 100) * (L + 1) ^ 3 := by
  simp [timePolynomial]

@[simp] theorem finalTapes_input (input output : List Bool) : finalTapes input output .input = input := rfl
@[simp] theorem finalTapes_output (input output : List Bool) : finalTapes input output .output = output := rfl

end MaxCutGames.Foundations.Complexity.MachineLazyTable

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

namespace MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label )

/-- A fixed explicit list of every non-output tape, independent of input data. -/
def cleanupTapes : List Tape :=
  [.input, .source, .vertices, .darts, .fuel, .vertex, .reverse,
    .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse, .rowBuffer]

end MaxCutGames.Foundations.Complexity.MachineLazyTableRuntime

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

def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

@[simp] theorem bitLength_zero : bitLength 0 = 0 := rfl

theorem bitLength_positive {n : Nat} (h : n ≠ 0) : bitLength n = n.log2 + 1 := by
  simp [bitLength, h]

def increments (n : Nat) (started : Bool) : Nat :=
  if n = 0 then (if started then 0 else 1) else bitLength n

@[simp] theorem increments_true (n : Nat) : increments n true = bitLength n := by
  by_cases hn : n = 0 <;> simp [increments, hn]

theorem increments_false (n : Nat) : increments n false = n.log2 + 1 := by
  by_cases hn : n = 0
  · subst n; rfl
  · simp [increments, bitLength, hn]

def coreTime (n : Nat) : Nat :=
  if h : n = 0 then 1 else n + n / 2 + 3 + coreTime (n / 2)
termination_by n
decreasing_by omega

@[simp] theorem coreTime_zero : coreTime 0 = 1 := by rw [coreTime]; rfl

theorem coreTime_positive {n : Nat} (h : n ≠ 0) :
    coreTime n = n + n / 2 + 3 + coreTime (n / 2) := by
  rw [coreTime, dite_eq_right h]

theorem coreTime_bound (n : Nat) : coreTime n ≤ 6 * n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp
    · rw [coreTime_positive hn]
      have smaller : n / 2 < n := by omega
      have bound := ih (n / 2) smaller
      omega

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := (Bool × Bool) × Option Bool

def initialState : State := ((false, false), none)

def rawTapes (input scratch output : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => scratch
  | 2 => output

theorem update_input_inline_MachineLogCounter (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 0 replacement = rawTapes replacement scratch output := by
  funext k
  fin_cases k <;> rfl

theorem update_scratch_inline_MachineLogCounter (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 1 replacement = rawTapes input replacement output := by
  funext k
  fin_cases k <;> rfl

theorem update_output_inline_MachineLogCounter (input scratch output replacement : List Bool) :
    Function.update (rawTapes input scratch output) 2 replacement = rawTapes input scratch replacement := by
  funext k
  fin_cases k <;> rfl

def stripLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push 1 (fun _ => true) (.goto fun _ => (1 : Fin 5)))
      (.load (fun _ => initialState) (.goto fun _ => 4)))

def guardLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .peek 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 2 (fun _ => true)
        (.load (fun _ => ((false, true), none)) (.goto fun _ => 3)))
      (.branch (fun state => state.1.2)
        (.load (fun _ => initialState) .halt)
        (.push 2 (fun _ => true) (.load (fun _ => initialState) .halt))))

def halfLoop : TM2.Stmt Alphabet (Fin 5) State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.branch (fun state => state.1.1)
        (.push 1 (fun _ => true)
          (.load (fun state => ((false, state.1.2), state.2)) (.goto fun _ => 3)))
        (.load (fun state => ((true, state.1.2), state.2)) (.goto fun _ => 3)))
      (.load (fun state => ((false, state.1.2), none)) (.goto fun _ => 4)))

def totalTime (n : Nat) : Nat := 2 * n + 3 + coreTime n

theorem totalTime_bound (n : Nat) : totalTime n ≤ 8 * n + 4 := by
  have bound := coreTime_bound n
  unfold totalTime
  omega

end MaxCutGames.Foundations.Complexity.MachineLogCounter

/-! A fixed Boolean-stack program prepending the logarithmic round count to
a graph table. It copies the original word, adds its two unary header values,
runs the actual logarithm machine, then emits the counter and original word. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterModel

open Turing

inductive ExtraTape
  | input | archive | scratch | output
  deriving DecidableEq

protected abbrev ExtraTape.enumList : List ExtraTape := [.input, .archive, .scratch, .output]

protected theorem ExtraTape.enumList_nodup : ExtraTape.enumList.Nodup := by decide

instance instFintypeExtraTape : Fintype ExtraTape where
  elems := ⟨ExtraTape.enumList, ExtraTape.enumList_nodup⟩
  complete x := by cases x <;> decide

inductive ExtraLabel
  | copyFirst | copySecond | seed | headerFirst | headerSecond
  | clearInput | clockCopy | archiveCopy | finalReverse
  deriving DecidableEq

protected abbrev ExtraLabel.enumList : List ExtraLabel := [.copyFirst, .copySecond, .seed,
  .headerFirst, .headerSecond, .clearInput, .clockCopy, .archiveCopy, .finalReverse]

protected theorem ExtraLabel.enumList_nodup : ExtraLabel.enumList.Nodup := by decide

instance instFintypeExtraLabel : Fintype ExtraLabel where
  elems := ⟨ExtraLabel.enumList, ExtraLabel.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Tape := Fin 3 ⊕ ExtraTape
abbrev Label := Fin 5 ⊕ ExtraLabel
abbrev Alphabet (_ : Tape) := Bool
abbrev State := MachineLogCounter.State × Option Bool

def initialState : State := (MachineLogCounter.initialState, none)

def clockLabel : Option (Fin 5) → Option Label
  | none => some (.inr .clearInput)
  | some l => some (.inl l)

/-- Homogeneous Boolean embedding of the fixed logarithm program. -/
def clockStatement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State →
    TM2.Stmt Alphabet Label State
  | .push k f next => .push (.inl k) (fun state => f state.1) (clockStatement next)
  | .peek k f next => .peek (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .pop k f next => .pop (.inl k) (fun state x => (f state.1 x, state.2)) (clockStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (clockStatement next)
  | .branch f yes no => .branch (fun state => f state.1) (clockStatement yes) (clockStatement no)
  | .goto f => .goto (fun state => .inl (f state.1))
  | .halt => .goto (fun _ => .inr .clearInput)

def readHeader (again next : Label) : TM2.Stmt Alphabet Label State :=
  .pop (.inr .input) (fun state head => (state.1, head))
    (.branch (fun state => state.2.getD false)
      (.push (.inl 0) (fun _ => true) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

def clockTapes (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool) : Tape → List Bool
  | .inl k => tapes k
  | .inr k => extra k

def clockConfiguration (extra : ExtraTape → List Bool) (register : Option Bool)
    (c : TM2.Cfg MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State) :
    TM2.Cfg Alphabet Label State := ⟨clockLabel c.l, (c.var, register), clockTapes c.stk extra⟩

theorem clockTapes_update (tapes : Fin 3 → List Bool) (extra : ExtraTape → List Bool)
    (k : Fin 3) (word : List Bool) :
    clockTapes (Function.update tapes k word) extra =
      Function.update (clockTapes tapes extra) (.inl k) word := by
  funext tape
  cases tape <;> simp [clockTapes, Function.comp_def]

theorem clockStatement_simulation (extra : ExtraTape → List Bool) (register : Option Bool)
    (statement : TM2.Stmt MachineLogCounter.Alphabet (Fin 5) MachineLogCounter.State)
    (state : MachineLogCounter.State) (tapes : Fin 3 → List Bool) :
    TM2.stepAux (clockStatement statement) (state, register) (clockTapes tapes extra) =
      clockConfiguration extra register (TM2.stepAux statement state tapes) := by
  induction statement generalizing state tapes with
  | push k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [clockStatement, TM2.stepAux, clockTapes] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simp only [clockStatement, TM2.stepAux, clockTapes]
      rw [← clockTapes_update]
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
      simpa only [clockStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [clockStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

end MaxCutGames.Foundations.Complexity.GraphCounterModel

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

namespace MaxCutGames.Foundations.Complexity.GraphCounterModel

open Turing

def startExtra (input archive : List Bool) : ExtraTape → List Bool
  | .input => input
  | .archive => archive
  | _ => []

def startMemory (input archive sum : List Bool) : Tape → List Bool
  | .inl k => if k = 0 then sum else []
  | .inr k => startExtra input archive k

theorem startMemory_input_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inr .input) replacement =
      startMemory replacement archive sum := by
  funext tape
  cases tape with
  | inl k => simp [startMemory]
  | inr k => cases k <;> simp [startMemory, startExtra]

theorem startMemory_sum_update (input archive sum replacement : List Bool) :
    Function.update (startMemory input archive sum) (.inl 0) replacement =
      startMemory input archive replacement := by
  funext tape
  cases tape with
  | inl k => by_cases h : k = 0 <;> simp [startMemory, h]
  | inr k => simp [startMemory]

end MaxCutGames.Foundations.Complexity.GraphCounterModel

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

def alphabet : Nat := 64
def compositionLoss : Nat := 12288
def denominator : Nat := 16 * alphabet ^ 4 * 66 * compositionLoss

end MaxCutGames.Foundations.PCP.FinalConstants

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace MaxCutGames.Foundations.PCP.RoundTables

theorem dartFactor_positive (q : Nat) : 0 < AlphabetGraphBounds.dartFactor q := by
  unfold AlphabetGraphBounds.dartFactor AlphabetGraphBounds.localEventFactor
  positivity

end MaxCutGames.Foundations.PCP.RoundTables

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

namespace MaxCutGames.Foundations.PCP.AmplificationIteration

def run {X : Type*} (step : X → X) : Nat → X → X
  | 0, x => x
  | n + 1, x => step (run step n x)

end MaxCutGames.Foundations.PCP.AmplificationIteration

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_GraphTableComplexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Concrete bridges between graph cardinality and the length of the validated
unary table encoding. These bounds supply the input-length and intermediate
encoding estimates used by actual machine trace composition; they are not
themselves a machine execution certificate.
-/

namespace MaxCutGames.Foundations.PCP.GraphTableComplexity

open MaxCutGames.Foundations.Complexity
open Polynomial

noncomputable def encodingPolynomial (q : Nat) : Polynomial Nat :=
  X ^ 2 + C (2 * (q * q) + 1) * X + C 2

theorem encodingPolynomial_eval (q n : Nat) :
    (encodingPolynomial q).eval n = n ^ 2 + (2 * (q * q) + 1) * n + 2 := by
  simp [encodingPolynomial]

theorem encodingPolynomial_mono (q : Nat) {n m : Nat} (hnm : n ≤ m) :
    (encodingPolynomial q).eval n ≤ (encodingPolynomial q).eval m := by
  rw [encodingPolynomial_eval, encodingPolynomial_eval]
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.pow_le_pow_left hnm 2) (Nat.mul_le_mul_left _ hnm)) 2

theorem rowBound_le_polynomial (q vertices darts : Nat) :
    vertices + darts + 2 + darts * (vertices + darts + 2 * (q * q)) ≤
      (encodingPolynomial q).eval (vertices + darts) := by
  have hd : darts ≤ vertices + darts := Nat.le_add_left darts vertices
  calc
    _ ≤ vertices + darts + 2 +
        (vertices + darts) * (vertices + darts + 2 * (q * q)) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
    _ = _ := by rw [encodingPolynomial_eval]; ring

end MaxCutGames.Foundations.PCP.GraphTableComplexity

/-!
The actual fixed-parameter graph transformation in one PCP amplification round.
It preprocesses the input graph, checks all edges of each bounded walk using
local endpoint labels, and applies the checked constant-query alphabet reduction.
The bounded address list is explicit fixed data shared by every input graph.
-/

/-!
# The actual first moment of an endpoint-opinion witness

The pivot factorization is applied to actual finite walks. Its two endpoint
operator bounds are obtained from the proved lazy-graph mixture and smoothing
theorem. No witness-event probability law is assumed.
-/

/-! The second moment of the actual marked-edge count in a consecutive walk
window. Pair events are reduced to the checked spectral return operator. -/

/-!
# The scalar bound for all positive error densities

The first lemma bounds a ratio using only a nonnegative coefficient bounded
by a positive cutoff. The second applies it to a positive natural count and
the first- and second-moment expressions in the powering argument.
-/

/-! The actual graph-powering soundness bound. Modal endpoint opinions give
the first moment, spectral return gives the second moment, and an actual
checked path constraint turns each witness into rejection. -/

/-!
# The fixed constants in the actual powering estimate

The six-bit alphabet has 64 letters. The middle window, endpoint length,
spectral parameter and composition loss in the checked powering theorem give
exactly the constants used in the final amplification round. Large natural
constants remain symbolic in these calculations.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialPredicate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

namespace MaxCutGames.Foundations.PCP.RawInitialRows

abbrev Signs := Bool × Bool × Bool
abbrev Names := Nat × Nat × Nat

end MaxCutGames.Foundations.PCP.RawInitialRows

/-! Exact ordered rows of the initial incidence table. Every relation retains
all 4096 entries, including repetitions; this is a list identity, not a runtime bound. -/

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

inductive Tape
  | input | «variables» | counter | index | field (slot : Fin 6)
  | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Alphabet (_ : Tape) := Bool

def nameField (slot : Fin 3) : Fin 6 := ⟨2 * slot.val, by omega⟩

end MaxCutGames.Foundations.PCP.RawInitialMachineModel

/-!
Actual execution of the raw initial graph machine from its standard input
configuration to the first clause-loop guard. The unread clause bits are
preserved verbatim, and all tape contents at the boundary are explicit.
-/

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

inductive Tape
  | input | output | accumulator | scratch | vertices | darts | tail | head | rowIndex
  | archive | reverseIndex | scanWork | indexWork
  deriving DecidableEq

protected abbrev Tape.enumList : List Tape := [.input, .output, .accumulator, .scratch,
  .vertices, .darts, .tail, .head, .rowIndex, .archive, .reverseIndex, .scanWork, .indexWork]

protected theorem Tape.enumList_nodup : Tape.enumList.Nodup := by decide

instance instFintypeTape : Fintype Tape where
  elems := ⟨Tape.enumList, Tape.enumList_nodup⟩
  complete x := by cases x <;> decide

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

def source : Fin 5 → Tape :=
  Fin.cases .vertices (Fin.cases .darts (Fin.cases .tail (Fin.cases .head (fun _ => .rowIndex))))

def headRoles : Fin 6 → Tape :=
  Fin.cases .archive (Fin.cases .reverseIndex (Fin.cases .scanWork
    (Fin.cases .indexWork (Fin.cases .head (fun _ => .scratch)))))

theorem headRoles_injective : Function.Injective headRoles := by
  decide

theorem source_ne_scratch (i : Fin 5) : source i ≠ Tape.scratch := by
  fin_cases i <;> decide

theorem source_ne_accumulator (i : Fin 5) : source i ≠ Tape.accumulator := by
  fin_cases i <;> decide

end Program

end MaxCutGames.Foundations.Complexity.FinalCNFMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFHeader
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The concrete final-CNF machine's entry phase. It archives its complete input,
reads the two unary size fields, emits the exact formula header, and reaches
the row guard. The transition witness is assembled from actual program calls.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open Turing
open PCP.AlphabetTable

/-- Explicit tape frame used during the header phase; all unlisted work tapes
are empty. The archive is separate from the unread input. -/
def headerFrame (input archive vertices darts rowIndex tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .archive => archive
  | .vertices => vertices
  | .darts => darts
  | .rowIndex => rowIndex
  | .tail => tail
  | .head => head
  | .accumulator => accumulator
  | _ => []

def headerInputTapes (input : List Bool) : Tape → List Bool :=
  headerFrame input [] [] [] [] [] [] []

/-- A fixed polynomial in the complete encoded input length. -/
noncomputable def headerTimePolynomial : Polynomial Nat :=
  Polynomial.C 25 * Polynomial.X + Polynomial.C 52

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

/-!
Actual finite-machine execution of the final converter's row phases. These
certificates use the concrete program statements, preserve all other tapes,
and expose the precise concatenated output of the fixed emission plan.
-/

/-!
# Structural conversion to the generic 64-label table format

The fixed and generic formats store exactly the same fields in the same order.
Conversion maps the row structure, keeping each endpoint, reversal index, and
relation vector unchanged. In particular, the serialized input bits are equal,
so the generic table lookup machine applies to the actual final-converter input.
-/

/-! Execution of one complete actual graph row in the final CNF machine. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Exact row enumeration and input/output stream identities for the concrete
final-CNF machine. Rows occur in stored order, including repeated rows.
-/

/-! The actual bounded loop over every stored row of the final CNF converter. -/

/-!
The complete actual output-producing trace of the final CNF machine. Its
terminal configuration still contains private work tapes before the
canonical halt required by the machine interface.
-/

/-!
Fixed literal templates for the twelve-query converter. All control data have
constant size: twelve query references, nine auxiliary references, ten clauses,
and three literal slots. Pattern bits remain symbolic throughout the proof.

These templates specify the actual serialized rows. Their machine execution
is proved separately in FinalCNFRow and FinalCNFComputation.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFTemplate

open PCP

inductive Reference where
  | query : Fin 12 → Reference
  | auxiliary : Fin 9 → Reference
  deriving DecidableEq

structure LiteralTemplate where
  reference : Reference
  positive : Bool
  deriving DecidableEq

abbrev ClauseTemplate := Vector LiteralTemplate 3

def queryLiteral (bits : Fin 12 → Bool) (i : Fin 12) : LiteralTemplate :=
  ⟨.query i, !(bits i)⟩

def auxiliaryLiteral (j : Fin 9) (positive : Bool) : LiteralTemplate :=
  ⟨.auxiliary j, positive⟩

def tautologyTemplate : ClauseTemplate :=
  #v[⟨.query 0, true⟩, ⟨.query 0, false⟩, ⟨.query 0, true⟩]

/-- The same prefix-chain clauses used by `splitLong`, in their output order. -/
def chainTemplates (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  #v[
    #v[queryLiteral bits 0, queryLiteral bits 1, auxiliaryLiteral 0 true],
    #v[auxiliaryLiteral 0 false, queryLiteral bits 2, auxiliaryLiteral 1 true],
    #v[auxiliaryLiteral 1 false, queryLiteral bits 3, auxiliaryLiteral 2 true],
    #v[auxiliaryLiteral 2 false, queryLiteral bits 4, auxiliaryLiteral 3 true],
    #v[auxiliaryLiteral 3 false, queryLiteral bits 5, auxiliaryLiteral 4 true],
    #v[auxiliaryLiteral 4 false, queryLiteral bits 6, auxiliaryLiteral 5 true],
    #v[auxiliaryLiteral 5 false, queryLiteral bits 7, auxiliaryLiteral 6 true],
    #v[auxiliaryLiteral 6 false, queryLiteral bits 8, auxiliaryLiteral 7 true],
    #v[auxiliaryLiteral 7 false, queryLiteral bits 9, auxiliaryLiteral 8 true],
    #v[auxiliaryLiteral 8 false, queryLiteral bits 10, queryLiteral bits 11]]

def blockTemplates (accepted : Bool) (bits : Fin 12 → Bool) : Vector ClauseTemplate 10 :=
  if accepted then Vector.replicate 10 tautologyTemplate else chainTemplates bits

def templates (accepted : Bool) (bits : Fin 12 → Bool) : List ClauseTemplate :=
  (blockTemplates accepted bits).toList

/-- Fixed clause/slot indexing for the machine's finite emission plan. -/
def literalAt (accepted : Bool) (bits : Fin 12 → Bool)
    (clause : Fin 10) (slot : Fin 3) : LiteralTemplate :=
  (blockTemplates accepted bits)[clause][slot]

def literalWords (index : Reference → Nat) (literal : LiteralTemplate) : List Nat :=
  [index literal.reference, if literal.positive then 1 else 0]

end MaxCutGames.Foundations.Complexity.FinalCNFTemplate

/-!
The fixed finite emission plan for one directed graph row. All choices based
on the relation are functions of its 4096-bit finite register. Vertex counts,
endpoint names and row indices are read by preserving unary scans.
-/

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

open Complexity

/-- A fixed quadratic in the full serialized input length. -/
noncomputable def sizePolynomial : Polynomial Nat :=
  Polynomial.C 77824 * Polynomial.X + Polynomial.C 2 +
    (Polynomial.C 40960 * Polynomial.X) *
      (Polynomial.C 3 * (Polynomial.C 36864 * Polynomial.X + Polynomial.C 2))

theorem sizePolynomial_eval (N : Nat) :
    sizePolynomial.eval N = 77824 * N + 2 + (40960 * N) * (3 * (36864 * N + 2)) := by
  simp [sizePolynomial]

end MaxCutGames.Foundations.PCP.FinalTableFormula

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinalCNFOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The final machine's complete output stream is the exact serialization of its
actual formula. This identity includes the two size fields, every clause and
literal field, and all unary delimiters. No desired output equality is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

open PCP

noncomputable def rowTimePolynomial : Polynomial Nat :=
  Polynomial.C 860160 * (Polynomial.C 3 * (Polynomial.X + Polynomial.C 1) + Polynomial.C 3) +
    Polynomial.C 12 * Polynomial.X + Polynomial.C 15

end MaxCutGames.Foundations.Complexity.FinalCNFMachine.Program

namespace MaxCutGames.Foundations.Complexity.FinalCNFCleanup

open Turing
open FinalCNFMachine.Program (Tape )

section Redirect

variable {K Λ Λ' σ : Type} {Γ : K → Type} [DecidableEq K]

def redirectLabel (labels : Λ → Λ') (haltTarget : Option Λ') : Option Λ → Option Λ'
  | none => haltTarget
  | some label => some (labels label)

def redirectCfg (labels : Λ → Λ') (haltTarget : Option Λ') (cfg : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ :=
  ⟨redirectLabel labels haltTarget cfg.l, cfg.var, cfg.stk⟩

/-- Structural redirection changes only the destinations of goto and halt. -/
def redirectStmt (labels : Λ → Λ') (haltTarget : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (redirectStmt labels haltTarget next)
  | .peek k f next => .peek k f (redirectStmt labels haltTarget next)
  | .pop k f next => .pop k f (redirectStmt labels haltTarget next)
  | .load f next => .load f (redirectStmt labels haltTarget next)
  | .branch test yes no => .branch test
      (redirectStmt labels haltTarget yes) (redirectStmt labels haltTarget no)
  | .goto label => .goto (fun state => labels (label state))
  | .halt => match haltTarget with
    | none => .halt
    | some label => .goto (fun _ => label)

theorem stepAux_redirect (labels : Λ → Λ') (haltTarget : Option Λ')
    (stmt : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (redirectStmt labels haltTarget stmt) state tapes =
      redirectCfg labels haltTarget (TM2.stepAux stmt state tapes) := by
  induction stmt generalizing state tapes with
  | push k f next ih => exact ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih => exact ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      exact ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => exact ih (f state) tapes
  | branch test yes no ihYes ihNo =>
      cases h : test state with
      | false => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [redirectStmt, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto label => rfl
  | halt => cases haltTarget <;> rfl

end Redirect

end MaxCutGames.Foundations.Complexity.FinalCNFCleanup

/-!
The complete polynomial-time machine certificate for converting a validated
64-label graph table into its actual 3CNF formula. The proof composes the real
input parser, all row executions, output reversal, and private-tape cleanup.
-/

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

def extraTapes (rest original : List Bool) : ExtraTape → List Bool
  | .input => rest
  | .archive => original
  | _ => []

def frame (input archive counter reversed output : List Bool) : Tape → List Bool
  | .inl i => if i = 2 then counter else []
  | .inr .input => input
  | .inr .archive => archive
  | .inr .scratch => reversed
  | .inr .output => output

theorem trace_trans_inline_GraphCounterFinish {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

end MaxCutGames.Foundations.Complexity.GraphCounterFinish

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

/-!
Actual unary-guard iteration for a logarithmic number of rounds. Semantic
cardinality grows by a fixed linear factor. A separate encoding polynomial
bounds each intermediate word; it is never iterated as a size recurrence.
The body hypotheses are individual executions of the supplied finite program.
-/

namespace MaxCutGames.Foundations.Complexity.PCPIterationMachine

open Turing
open MachineCountedLoop

def rounds (n : Nat) : Nat := n.log2 + 1

theorem rounds_le (n : Nat) : rounds n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem two_pow_rounds_le (n : Nat) : 2 ^ rounds n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; decide
  · have h := Nat.log2_self_le hn
    simp only [rounds, pow_succ]
    omega

/-- The exponent is a fixed growth constant, independent of the input. -/
theorem growth_pow_rounds_le (growth n : Nat) :
    growth ^ rounds n ≤ (2 * (n + 1)) ^ growth := by
  calc
    growth ^ rounds n ≤ (2 ^ growth) ^ rounds n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := growth))) _
    _ = (2 ^ rounds n) ^ growth := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 1)) ^ growth := Nat.pow_le_pow_left (two_pow_rounds_le n) growth

def sizeEnvelope (growth n : Nat) : Nat := (n + 1) * (2 * (n + 1)) ^ growth

/-- This recurrence concerns semantic cardinality, not unary encoding length. -/
theorem semanticSize_geometric (sizes : Nat → Nat) (growth n : Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ (n + 1) * growth ^ i := by
  induction i with
  | zero => simpa only [pow_zero, Nat.mul_one] using initialBound
  | succ i ih =>
    have ilt : i < rounds n := by omega
    calc
      sizes (i + 1) ≤ growth * sizes i := growthBound i ilt
      _ ≤ growth * ((n + 1) * growth ^ i) :=
        Nat.mul_le_mul_left growth (ih (by omega))
      _ = (n + 1) * growth ^ (i + 1) := by rw [pow_succ]; ac_rfl

theorem semanticSize_bound (sizes : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ sizeEnvelope growth n := by
  calc
    sizes i ≤ (n + 1) * growth ^ i :=
      semanticSize_geometric sizes growth n initialBound growthBound i hi
    _ ≤ (n + 1) * growth ^ rounds n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right growthPositive hi)
    _ ≤ sizeEnvelope growth n :=
      Nat.mul_le_mul_left _ (growth_pow_rounds_le growth n)

noncomputable def sizePolynomial (growth : Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (2 * (Polynomial.X + 1)) ^ growth

@[simp] theorem sizePolynomial_eval (growth n : Nat) :
    (sizePolynomial growth).eval n = sizeEnvelope growth n := by
  simp [sizePolynomial, sizeEnvelope]

end MaxCutGames.Foundations.Complexity.PCPIterationMachine

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Clone100Counting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete clone sample space. Global distinctness is a stronger
conditioning rule than distinctness only at repeated original «variables».
It retains the same 3/100 bound and makes the number of copies uniform. -/

namespace MaxCutGames.Outer.Clone100

open MaxCutGames.Reduction CloneGap
open scoped BigOperators

noncomputable section

def nameEquiv (n : Nat) : Fin n × Fin 100 ≃ Fin (n * 100) := finProdFinEquiv

end
end MaxCutGames.Outer.Clone100

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FinishBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scalar estimates for the last paragraph of the v2 construction. These lemmas
only perform the stated rounding/subdivision/repetition arithmetic; they do
not assume or assert an unproved repetition theorem or hardness result.
-/

namespace MaxCutGames.Explicit.FinishBounds

theorem subdivision_completeness (vH vB d τ : ℝ)
    (hH : 1 - d ≤ vH)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    1 - (d + τ) / 4 ≤ vB := by
  have h := (abs_le.mp hround).1
  linarith

theorem subdivision_soundness (vH vB τ : ℝ)
    (hH : vH ≤ 99 / 100) (hτ : τ ≤ 1 / 200)
    (hround : |vB - (1 - (1 - vH) / 4)| ≤ τ / 4) :
    vB ≤ 1 - 1 / 800 := by
  have h := (abs_le.mp hround).2
  linarith

/-- The full completeness loss after the coordinatewise product labeling. -/
theorem final_completeness (vB vG d τ ε₀ ε : ℝ) (t : Nat) (ht : 0 < t)
    (hB : 1 - (d + τ) / 4 ≤ vB)
    (hG : 1 - (t : ℝ) * (1 - vB) ≤ vG)
    (hd : d ≤ ε₀ / t) (hτ : τ ≤ ε₀ / t)
    (hε₀ : 0 ≤ ε₀) (hε : ε₀ ≤ ε) :
    1 - ε ≤ vG := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hd' := (le_div_iff₀ ht').mp hd
  have hτ' := (le_div_iff₀ ht').mp hτ
  have hB' : (t : ℝ) * (1 - vB) ≤ t * ((d + τ) / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) ht'.le
  nlinarith

end MaxCutGames.Explicit.FinishBounds

/-!
The outer error parameters are fixed before the latent gadget or its alphabet.
We use the same positive reciprocal integer for the latent noise budget and
the rounding tolerance. This permitted specialization makes uniform occurrence
rounding an exact fixed-copy operation. The later parity error is chosen only
after the tuple length has been fixed.
-/

namespace MaxCutGames.ParameterSelection
noncomputable section

structure OuterParameters (ε δ : ℝ) where
  epsilon0 : ℚ
  delta0 : ℚ
  epsilon0_pos : 0 < epsilon0
  delta0_pos : 0 < delta0
  epsilon0_le : (epsilon0 : ℝ) ≤ ε
  delta0_le : (delta0 : ℝ) ≤ δ
  repetitions : ℕ
  repetitions_pos : 0 < repetitions
  soundness_rate : (1 - (1 : ℝ) / 10240000) ^ repetitions ≤ delta0
  copies : ℕ
  copies_large : 200 ≤ copies
  reciprocal_pos : (0 : ℚ) < 1 / copies
  reciprocal_small : 1 / (copies : ℚ) ≤ 1 / 200
  reciprocal_budget : 1 / (copies : ℚ) ≤ epsilon0 / repetitions

namespace OuterParameters

variable {ε δ : ℝ} (P : OuterParameters ε δ)

def pStar : ℚ := 1 / P.copies

theorem pStar_pos : 0 < P.pStar := P.reciprocal_pos

end OuterParameters
end
end MaxCutGames.ParameterSelection

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRhsLoad
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Reduction.MachineRhsLoad

open Turing
open MaxCutGames.Foundations.Complexity

def fill {k : Nat} (values initial : Fin k → Bool) (cells : List (Fin k)) : Fin k → Bool :=
  cells.foldl (fun current i => Function.update current i (values i)) initial

variable {k : Nat} {K Λ σ : Type} [DecidableEq K]

def readRhs (field : Fin k → K) (tapes : K → List Bool) : Fin k → Bool :=
  fun i => (tapes (field i)).head?.getD false

end MaxCutGames.Reduction.MachineRhsLoad

/-! Execute all fixed outcome rows after the existing RHS loader. A single
dispatcher freezes the loaded finite RHS vector into labels. Every row is an
actual address-edge phase; no row-run or whole-loop execution is assumed.
Program definitions contain only fixed templates, literal permutations, and
tape/label placement. Numeric names, radix, and capacity occur only in tapes
and the semantic correctness hypotheses. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OccurrenceTupleOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact coordinate-order bridge from the checked tuple odometer to the
outer reduction's occurrence enumeration. The odometer changes coordinate zero
fastest; `ActualEnumeration.functions` changes it slowest. Reading saved digit
`j.rev` as query coordinate `j` matches the complete ordered list. No primitive
machine or assumed whole-loop runtime is introduced here. -/

namespace MaxCutGames.Integration.AddressTupleBudget

open Reduction Foundations.Complexity

variable {k s d noiseCount : Nat}

def radixBound (s d L : Nat) : Nat := L + (2^s + 2^d + 4)

def magnitude (k s d L : Nat) : Nat :=
  (L+1) + radixBound s d L + (radixBound s d L)^(1+9*k) +
    (1+9*k)*(radixBound s d L+1) + 1

noncomputable def magnitudePolynomial (k s d : Nat) : Polynomial Nat :=
  (Polynomial.X+1) + (Polynomial.X+Polynomial.C (2^s+2^d+4)) +
    (Polynomial.X+Polynomial.C (2^s+2^d+4))^(1+9*k) +
    Polynomial.C (1+9*k)*(Polynomial.X+Polynomial.C (2^s+2^d+4)+1) + 1

end MaxCutGames.Integration.AddressTupleBudget

/-!
# Polynomial encoded length of the actual output

The encoder uses a unary, delimited forward-permutation
format. The instance is the actual list-based reduction, including canonical
body deduplication and every repeated edge occurrence. The polynomial's
coefficients depend only on the fixed gadget table and tuple dimensions.

These are output-length theorems. They do not assert a machine running-time
certificate for canonicalization, enumeration, or serialization.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Model2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite occurrence presentations used by the v2 rounding/subdivision construction.
An occurrence has its own identifier: its endpoints need not be distinct and
different occurrences may have the same endpoints. The bipartite target records
injectivity of the pair of endpoints, which is precisely the required simplicity.
No hardness or analytic premise enters these structures.
-/

namespace MaxCutGames.Explicit

structure OccurrenceGame (V E A : Type*) where
  source : E → V
  target : E → V
  permutation : E → Equiv.Perm A

end MaxCutGames.Explicit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The four-edge subdivision.
Every input occurrence has its own three interior vertices, even when
the original endpoints coincide or another occurrence has the same endpoints.
The left/right presentation inverts the permutation on the fourth edge.
-/

namespace MaxCutGames.Explicit

open scoped BigOperators

namespace OccurrenceGame

variable {V E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : OccurrenceGame V E A) (a : V → A) : Nat :=
  ∑ e, if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0

variable [Fintype V] [Fintype A]

noncomputable def maxSatisfied (g : OccurrenceGame V E A) : Nat := by
  classical
  exact Finset.univ.sup (satisfiedCount g)

noncomputable def value (g : OccurrenceGame V E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : OccurrenceGame V E A) (a : V → A) :
    satisfiedCount g a ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := satisfiedCount g) (Finset.mem_univ a)

theorem maxSatisfied_attained [Nonempty A] (g : OccurrenceGame V E A) :
    ∃ a, satisfiedCount g a = maxSatisfied g := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (satisfiedCount g)
  exact ⟨a, ha.symm⟩

end OccurrenceGame

namespace Subdivision

variable {V E A : Type*}

/-- Original vertices and the middle vertices `q_e`. -/
abbrev Left (V E : Type*) := V ⊕ E

/-- `false` is `p_e`, and `true` is `r_e`. -/
abbrev Right (E : Type*) := E × Bool

abbrev Edge (E : Type*) := E × Fin 4

def left (g : OccurrenceGame V E A) (ei : Edge E) : Left V E :=
  if ei.2 = 0 then Sum.inl (g.source ei.1)
  else if ei.2 = 3 then Sum.inl (g.target ei.1)
  else Sum.inr ei.1

def right (ei : Edge E) : Right E := (ei.1, decide (2 ≤ ei.2.val))

def permutation (g : OccurrenceGame V E A) (ei : Edge E) : Equiv.Perm A :=
  if ei.2 = 3 then (g.permutation ei.1).symm else Equiv.refl A

/-- The private occurrence identifier prevents parallel edges after subdivision.
This also handles a loop, which becomes a genuine four-cycle. -/
theorem endpoints_injective (g : OccurrenceGame V E A) :
    Function.Injective (fun ei : Edge E => (left g ei, right ei)) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ h
  have hef : e = f := congrArg (fun x => x.2.1) h
  subst f
  fin_cases i <;> fin_cases j <;> simp_all [left, right]

/-- Restrict any output labeling to the original vertices. -/
def restrict (a : Left V E → A) : V → A := fun v => a (Sum.inl v)

def extendLeft (g : OccurrenceGame V E A) (a : V → A) : Left V E → A :=
  Sum.elim a (fun e => a (g.source e))

def extendRight (g : OccurrenceGame V E A) (a : V → A) : Right E → A :=
  fun eb => a (g.source eb.1)

@[simp] theorem restrict_extendLeft (g : OccurrenceGame V E A) (a : V → A) :
    restrict (extendLeft g a) = a := rfl

variable [DecidableEq A]

/-- The strongest possible path score for fixed endpoint labels is exactly
three plus the old satisfaction indicator. -/
theorem local_count_le (ρ : Equiv.Perm A) (u p q r v : A) :
    (if u = p then 1 else 0) + (if q = p then 1 else 0) +
      (if q = r then 1 else 0) + (if ρ.symm v = r then 1 else 0) ≤
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h₀ : u = p <;> by_cases h₁ : q = p <;>
    by_cases h₂ : q = r <;> by_cases h₃ : ρ.symm v = r <;>
    by_cases h : ρ u = v <;> simp_all [Equiv.symm_apply_eq]

theorem local_count_extend (ρ : Equiv.Perm A) (u v : A) :
    (if u = u then 1 else 0) + (if u = u then 1 else 0) +
      (if u = u then 1 else 0) + (if ρ.symm v = u then 1 else 0) =
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h : ρ u = v
  · have h' : ρ.symm v = u := by rw [← h, ρ.symm_apply_apply]
    simp [h, h']
  · have h' : ρ.symm v ≠ u := by
      intro he
      apply h
      rw [← he, ρ.apply_symm_apply]
    simp [h, h']

variable [Fintype E]

@[simp] theorem edge_count : Fintype.card (Edge E) = 4 * Fintype.card E := by
  simp [Edge, Nat.mul_comm]

@[simp] theorem left_count [Fintype V] :
    Fintype.card (Left V E) = Fintype.card V + Fintype.card E := by
  simp [Left]

@[simp] theorem right_count : Fintype.card (Right E) = 2 * Fintype.card E := by
  simp [Right, Nat.mul_comm]

end Subdivision

end MaxCutGames.Explicit

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_ProductTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Explicit numbered permutation-table outputs for bipartite graphs and products.
All numbering maps are supplied as actual equivalences; the product uses the
computable radix equivalence with division/remainder inverse, never an arbitrary
finite-type enumeration. The value bridge preserves every list occurrence.
-/

namespace MaxCutGames.Explicit.ProductTarget

open MaxCutGames.Foundations
open scoped BigOperators

variable {L R E : Type*} {q N M : ℕ}

section Value

variable [Fintype L] [Fintype R] [Fintype E]

def mergeLabelings (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) : Fin N → Fin q :=
  fun v => Sum.elim left right (vertices.symm v)

omit [Fintype L] [Fintype R] in
@[simp] theorem mergeLabelings_left (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) (x : L) :
    mergeLabelings vertices left right (vertices (Sum.inl x)) = left x := by
  simp [mergeLabelings]

omit [Fintype L] [Fintype R] in
@[simp] theorem mergeLabelings_right (vertices : (L ⊕ R) ≃ Fin N)
    (left : L → Fin q) (right : R → Fin q) (y : R) :
    mergeLabelings vertices left right (vertices (Sum.inr y)) = right y := by
  simp [mergeLabelings]

end Value

/-- The explicit address and `ofDigits` share the same least-significant-first
coordinate order, with no restriction on the radix beyond the digit type. -/
theorem address_eq_ofDigits {n t : ℕ} (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) = Nat.ofDigits n (List.ofFn (fun i => (f i : ℕ))) := by
  have hmap :
      (List.ofFn (fun i => (f i : ℕ))).mapIdx (fun i a => a * n ^ i) =
        List.ofFn (fun i : Fin t => (f i : ℕ) * n ^ (i : ℕ)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  rw [finFunctionFinEquiv_apply, Nat.ofDigits_eq_sum_mapIdx, hmap, List.sum_ofFn]

/-- A forward Horner controller reads the coordinate words in reverse order.
This is a word-order identity, separate from its machine execution theorem. -/
theorem address_eq_horner {n t : ℕ} (f : Fin t → Fin n) :
    (finFunctionFinEquiv f : ℕ) =
      (List.ofFn (fun i => (f i : ℕ))).reverse.foldl
        (fun acc digit => n * acc + digit) 0 := by
  rw [address_eq_ofDigits, Nat.ofDigits_eq_foldr, List.foldl_reverse]
  simp only [Nat.cast_id, Nat.add_comm]

end MaxCutGames.Explicit.ProductTarget

/-!
Concrete numbered, full-table output for the v2 four-edge subdivision.
Original vertices keep their names. The new names are `n+e`, `n+Q+2e`,
and `n+Q+2e+1`, and each input occurrence emits four consecutive rows.
-/

namespace MaxCutGames.Explicit.SubdivisionTarget

open MaxCutGames.Foundations
open scoped BigOperators

/-- Number `p_e` by `2e` and `r_e` by `2e+1`. -/
def numericRightEquiv (Q : Nat) : Fin Q × Bool ≃ Fin (Q * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin Q)) finTwoEquiv.symm).trans finProdFinEquiv

@[simp] theorem numericRightEquiv_false_val (Q : Nat) (e : Fin Q) :
    (numericRightEquiv Q (e, false)).val = 2 * e.val := by
  change 0 + 2 * e.val = 2 * e.val
  exact Nat.zero_add _

@[simp] theorem numericRightEquiv_true_val (Q : Nat) (e : Fin Q) :
    (numericRightEquiv Q (e, true)).val = 2 * e.val + 1 := by
  change 1 + 2 * e.val = 2 * e.val + 1
  exact Nat.add_comm _ _

/-- Original vertices, middle vertices, then interleaved `p_e,r_e`. -/
def numericVertexEquiv (n Q : Nat) :
    (Fin n ⊕ Fin Q) ⊕ (Fin Q × Bool) ≃ Fin (n + 3 * Q) :=
  ((Equiv.sumCongr
      (finSumFinEquiv : Fin n ⊕ Fin Q ≃ Fin (n + Q))
      (numericRightEquiv Q)).trans
    (finSumFinEquiv : Fin (n + Q) ⊕ Fin (Q * 2) ≃ Fin ((n + Q) + Q * 2))).trans
      (finCongr (by ring : (n + Q) + Q * 2 = n + 3 * Q))

@[simp] theorem numericVertexEquiv_original_val (n Q : Nat) (v : Fin n) :
    (numericVertexEquiv n Q (Sum.inl (Sum.inl v))).val = v.val := rfl

@[simp] theorem numericVertexEquiv_middle_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inl (Sum.inr e))).val = n + e.val := rfl

@[simp] theorem numericVertexEquiv_p_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inr (e, false))).val = n + Q + 2 * e.val := by
  change n + Q + (0 + 2 * e.val) = n + Q + 2 * e.val
  rw [Nat.zero_add]

@[simp] theorem numericVertexEquiv_r_val (n Q : Nat) (e : Fin Q) :
    (numericVertexEquiv n Q (Sum.inr (e, true))).val = n + Q + 2 * e.val + 1 := by
  change n + Q + (1 + 2 * e.val) = n + Q + 2 * e.val + 1
  omega

/-- The occurrence `e` occupies output indices `4e,4e+1,4e+2,4e+3`. -/
def numericEdgeEquiv (Q : Nat) : Fin (4 * Q) ≃ Fin Q × Fin 4 :=
  (finCongr (Nat.mul_comm 4 Q)).trans finProdFinEquiv.symm

@[simp] theorem numericEdgeEquiv_symm_val (Q : Nat) (e : Fin Q) (i : Fin 4) :
    ((numericEdgeEquiv Q).symm (e, i)).val = 4 * e.val + i.val := by
  change i.val + 4 * e.val = 4 * e.val + i.val
  exact Nat.add_comm _ _

end MaxCutGames.Explicit.SubdivisionTarget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Product
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The independent graph product in the last step of the v2 reduction.

Edges are tuples of actual base edges.  The endpoint maps remain injective,
the edge law is exactly uniform, and the associated game agrees with ordinary
parallel repetition for every pair of local strategies, including strategies
depending on their whole question tuples.  Only the completeness lower bound
uses coordinatewise strategies; no repetition soundness bound is assumed here.
-/

/-!
Machine-friendly product numbering on the common global vertex base.
Both endpoints use the same radix, so the machine needs neither a right-side
subtraction nor a final offset. Mixed-side tuples are isolated vertices. For a
positive repetition count the first coordinate supplies a total bipartition.
-/

namespace MaxCutGames.Explicit.ProductPaddedOutput

open MaxCutGames.Foundations
open ProductTarget
open scoped BigOperators

namespace Embedded

variable {L R E : Type*} {q N M : ℕ}

variable [Fintype L] [Fintype R] [Fintype E]

noncomputable def extendLabelings [Nonempty (Fin q)]
    (vertices : (L ⊕ R) ↪ Fin N) (left : L → Fin q) (right : R → Fin q) :
    Fin N → Fin q :=
  Function.extend vertices (Sum.elim left right) (fun _ => Classical.choice inferInstance)

end Embedded

end MaxCutGames.Explicit.ProductPaddedOutput

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineClone100Table
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The literal four-word row used by the hundred-clone finite machine. The
natural-number triple is a fixed program parameter; its bounds and distinctness
are needed only when identifying the output with the typed parity instance.
-/

namespace MaxCutGames.Explicit.MachineClone100Model

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad

inductive Tape
  | input | header | counter | field (slot : Fin 4) | scratch | reversed | output
  deriving DecidableEq, Fintype

abbrev Context (D : Nat) := Fin 2 ⊕ (Fin D × Fin 4)
abbrev State (D : Nat) := (Unit × Context D) × Option Bool
abbrev Alphabet (_ : Tape) := Bool

inductive Label (D : Nat)
  | headerStart (slot : Fin 2)
  | headerLoop (slot : Fin 2)
  | setup (context : Context D)
  | scan (context : Context D)
  | emit (context control : Context D) (symbol : Bool)
  | restore (context : Context D)
  | clearHeader
  | guard
  | fieldStart (slot : Fin 4)
  | fieldLoop (slot : Fin 4)
  | cleanup (slot : Fin 4)
  | finalCounter
  | finalReverse
  deriving DecidableEq, Fintype

def defaultControl (D : Nat) : Context D := .inl 0
def initialState (D : Nat) : State D := (((), defaultControl D), none)

def headerTape (j : Fin 2) : Tape := if j.val = 0 then .header else .counter

def contextSource {D : Nat} : Context D → Tape
  | .inl j => headerTape j
  | .inr p => .field p.2

def contextScale {D : Nat} : Context D → Nat
  | .inl j => if j.val = 0 then 100 else D
  | .inr p => if p.2.val < 3 then 100 else 1

def tripleField (t : Nat × Nat × Nat) (j : Fin 4) : Nat :=
  match j.val with
  | 0 => t.1
  | 1 => t.2.1
  | 2 => t.2.2
  | _ => 0

def contextOffset (triples : List (Nat × Nat × Nat)) : Context triples.length → Nat
  | .inl _ => 0
  | .inr p => tripleField (triples.get p.1) p.2

def contextNext {D : Nat} : Context D → Option (Label D)
  | .inl j => if j.val = 0 then some (.setup (.inl 1)) else some .clearHeader
  | .inr (i, j) =>
      if hj : j.val + 1 < 4 then some (.setup (.inr (i, ⟨j.val + 1, hj⟩)))
      else if hi : i.val + 1 < D then some (.setup (.inr (⟨i.val + 1, hi⟩, 0)))
      else some (.cleanup 0)

def cleanupNext {D : Nat} (j : Fin 4) : Label D :=
  if hj : j.val + 1 < 4 then .cleanup ⟨j.val + 1, hj⟩ else .guard

def drain {D : Nat} (tape : Tape) (again next : Label D) :
    TM2.Stmt Alphabet (Label D) (State D) :=
  .pop tape (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (.goto fun _ => next)))

end MaxCutGames.Explicit.MachineClone100Model

namespace MaxCutGames.Explicit.MachineClone100Context

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MachineClone100Model

theorem contextSource_ne_scratch {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.scratch := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

theorem contextSource_ne_reversed {D : Nat} (context : Context D) :
    contextSource context ≠ Tape.reversed := by
  cases context with
  | inl slot =>
    simp only [contextSource, headerTape]
    split <;> simp
  | inr pair => simp [contextSource]

end MaxCutGames.Explicit.MachineClone100Context

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineClone100Triples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.MachineClone100Triples

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MachineClone100Model MachineClone100Context

theorem chain_inline_MachineClone100Triples {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (first : f^[m] x = y) (second : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, first, second]

def affineRecord (a b c rhs : Nat) (t : Nat × Nat × Nat) : List Nat :=
  [t.1 + 100 * a, t.2.1 + 100 * b, t.2.2 + 100 * c, rhs]

end MaxCutGames.Explicit.MachineClone100Triples

namespace MaxCutGames.Explicit.MachineClone100Loop

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineClone100Model

structure Record where
  a : Nat
  b : Nat
  c : Nat
  rhs : Nat

def recordWords (r : Record) : List Nat := [r.a, r.b, r.c, r.rhs]

end MaxCutGames.Explicit.MachineClone100Loop

namespace MaxCutGames.Explicit.MachineClone100Certified

open MaxCutGames.Reduction

open Turing
open MaxCutGames.Foundations.Complexity

noncomputable def timePolynomial (copies : Nat) : Polynomial Nat :=
  Polynomial.C (300 * copies) * Polynomial.X * Polynomial.X +
    Polynomial.C (120 + 18 * copies) * Polynomial.X + Polynomial.C 23

theorem timePolynomial_eval (copies length : Nat) :
    (timePolynomial copies).eval length =
      (300 * copies) * length * length + (120 + 18 * copies) * length + 23 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]

theorem numericalBudget_inline_MachineClone100Certified (D N n m B out : Nat)
    (hn : n ≤ N) (hm : m ≤ N) (hB : B ≤ N)
    (ho : out ≤ (300 * D) * N * N + (100 + 3 * D) * N + 2) :
    (out + 2) + (((2 + 3 * D) * B + (9 + 12 * D) * m + 1) +
      (5 * n + 4 * m + 18)) ≤ (300 * D) * N * N + (120 + 18 * D) * N + 23 := by
  have hn' := Nat.mul_le_mul_left 5 hn
  have hm' := Nat.mul_le_mul_left (13 + 12 * D) hm
  have hb' := Nat.mul_le_mul_left (2 + 3 * D) hB
  calc
    _ = 5 * n + (13 + 12 * D) * m + (2 + 3 * D) * B + out + 21 := by ring
    _ ≤ 5 * N + (13 + 12 * D) * N + (2 + 3 * D) * N +
        ((300 * D) * N * N + (100 + 3 * D) * N + 2) + 21 := by omega
    _ = _ := by ring

end MaxCutGames.Explicit.MachineClone100Certified

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineClone100
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.MachineClone100

open Turing MaxCutGames.Reduction
open MaxCutGames.Foundations.Complexity

noncomputable section

theorem serialized_polynomial_inline_MachineClone100 (D N n m : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    n * 100 + m * D + 2 + m * D * (300 * n + 2) ≤
      (300 * D) * N * N + (100 + 3 * D) * N + 2 := by
  have hproduct := Nat.mul_le_mul_left (300 * D) (Nat.mul_le_mul hm hn)
  have hvariables := Nat.mul_le_mul_left 100 hn
  have hoccurrences := Nat.mul_le_mul_left (3 * D) hm
  calc
    _ = (300 * D) * (m * n) + 100 * n + (3 * D) * m + 2 := by ring
    _ ≤ (300 * D) * (N * N) + 100 * N + (3 * D) * N + 2 :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hproduct hvariables) hoccurrences)
        (Nat.le_refl 2)
    _ = _ := by ring

end

end MaxCutGames.Explicit.MachineClone100

/-!
A finite-state validator for the concrete ordinary-binary formula encoding.
It checks clause and literal framing, canonical name payloads, and the unique
terminal formula marker. The last-digit register starts at true for each name,
so the empty payload is accepted as zero while a nonempty payload must end in
one. Every bit following the terminal formula marker causes rejection.
-/

/-!
Total raw-input preprocessing for the ordinary binary formula codec. The
machine copies each input bit onto a reverse stack while running the finite
validator. Accepted words are restored verbatim; rejected words are drained
and replaced by the fixed contradictory formula. All three stack alphabets
and all control/register types are finite.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineProductGatherBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual work stacks left by the preserving gather. These
bounds justify clearing the query/scan remnants after each product field;
they are consequences of the exact tape formulas, not runtime assumptions. -/

/-! The product-field machine restores every work tape and appends precisely
one field to the reversed output. This boundary is strong enough to compose
all fields and every odometer visit without retaining an unbounded history. -/

namespace MaxCutGames.Explicit.MachineProductField

open MaxCutGames.Foundations.Complexity

variable {K : Type} [DecidableEq K] {width : Nat}

omit [DecidableEq K] in
@[simp] theorem mem_clearTapes (slots : Layout width ↪ K) (k : K) :
    k ∈ clearTapes slots ↔ k = slots (.inl (.inl 1)) ∨
      k = slots (.inl (.inl 2)) ∨ ∃ i, k = slots (.inl (.inr (.inr i))) := by
  simp [clearTapes, List.mem_ofFn, eq_comm]

omit [DecidableEq K] in
theorem extra_not_mem_clearTapes (slots : Layout width ↪ K) (i : Fin 7) :
    slots (.inr i) ∉ clearTapes slots := by
  simp only [mem_clearTapes]
  rintro (h | h | ⟨j, h⟩)
  · exact slots.injective.ne (by simp) h
  · exact slots.injective.ne (by simp) h
  · exact slots.injective.ne (by simp) h

omit [DecidableEq K] in
theorem Ready.empty_clearTapes (slots : Layout width ↪ K) (base : K → List Bool)
    (ready : Ready slots base) (k : K) (member : k ∈ clearTapes slots) : base k = [] := by
  rcases (mem_clearTapes slots k).mp member with rfl | rfl | ⟨i, rfl⟩
  · exact ready.query
  · exact ready.scan
  · exact ready.fields i

/-- The output update preserves all work-tape entry conditions. -/
theorem Ready.output_update (slots : Layout width ↪ K) (base : K → List Bool)
    (ready : Ready slots base) (word : List Bool) :
    Ready slots (Function.update base (slots (.inr 6)) word) := by
  have other (a : Layout width) (h : a ≠ .inr 6) :
      Function.update base (slots (.inr 6)) word (slots a) = base (slots a) :=
    Function.update_of_ne (slots.injective.ne h) _ _
  constructor
  · rw [other _ (by simp)]; exact ready.query
  · rw [other _ (by simp)]; exact ready.scan
  · rw [other _ (by simp)]; exact ready.gatherScratch
  · intro i; rw [other _ (by simp)]; exact ready.fields i
  · rw [other _ (by simp)]; exact ready.accA
  · rw [other _ (by simp)]; exact ready.accB
  · rw [other _ (by simp)]; exact ready.counter
  · rw [other _ (by simp)]; exact ready.hornerScratch
  · rw [other _ (by simp)]; exact ready.output

omit [DecidableEq K] in
theorem clearTapes_length (slots : Layout width ↪ K) : (clearTapes slots).length = width + 2 := by
  simp [clearTapes]

end MaxCutGames.Explicit.MachineProductField

/-! A finite row-field schedule. Endpoint fields use the input vertex radix;
permutation fields use the fixed alphabet radix. The complete list of columns
is in finite control, while all row indices, table entries and radix magnitudes
remain data on tapes. -/

namespace MaxCutGames.Explicit.MachineProductRow

open Turing
open MaxCutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K] {width : Nat}

abbrev Layout (width : Nat) := MachineProductField.Layout width ⊕ Unit
abbrev Command (width : Nat) := Bool × (Fin width → Nat)

/-- Only the radix tape is switched between endpoint and alphabet fields. -/
def fieldRole (useAlphabet : Bool) : MachineProductField.Layout width → Layout width
  | .inr 0 => if useAlphabet then .inr () else .inl (.inr 0)
  | tape => .inl tape

theorem fieldRole_injective (useAlphabet : Bool) :
    Function.Injective (fieldRole (width := width) useAlphabet) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => simpa [fieldRole] using h
    | inr b => fin_cases b <;> cases useAlphabet <;> simp [fieldRole] at h
  | inr a =>
    cases b with
    | inl b => fin_cases a <;> cases useAlphabet <;> simp [fieldRole] at h
    | inr b => fin_cases a <;> fin_cases b <;> cases useAlphabet <;> simp_all [fieldRole]

def fieldSlots (slots : Layout width ↪ K) (useAlphabet : Bool) :
    MachineProductField.Layout width ↪ K :=
  Function.Embedding.trans ⟨fieldRole useAlphabet, fieldRole_injective useAlphabet⟩ slots

def outputTape (slots : Layout width ↪ K) : K := slots (.inl (.inr 6))

end MaxCutGames.Explicit.MachineProductRow

/-!
The exact table lookups and field schedule consumed by the product machine.
The table contains rows only: the three input header words have already been
consumed, so each affine lookup has coefficient `q+2` and no header offset.
-/

namespace MaxCutGames.Explicit.ProductMachineSemantics

open MaxCutGames.Foundations
open Complexity

variable {n q t : ℕ}

def reverseDigits (fields : Fin t → ℕ) (i : ℕ) : ℕ :=
  if h : i < t then fields (Fin.rev ⟨i, h⟩) else 0

@[simp] theorem reverseDigits_at (fields : Fin t → ℕ) (i : Fin t) :
    reverseDigits fields i.val = fields i.rev := by simp [reverseDigits, i.isLt]

theorem reverseDigits_words (fields : Fin t → ℕ) :
    (List.range t).map (reverseDigits fields) = (List.ofFn fields).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < t := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, reverseDigits, hi', ↓reduceDIte,
      List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Fin.rev]
    apply congrArg fields
    apply Fin.ext
    change t - (i + 1) = t - 1 - i
    omega

def sourceCommand (t : ℕ) : MachineProductRow.Command t := (false, fun _ => 0)
def targetCommand (t : ℕ) : MachineProductRow.Command t := (false, fun _ => 1)
def imageCommand (q t : ℕ) (a : Fin (q ^ t)) : MachineProductRow.Command t :=
  (true, fun i => 2 + (finFunctionFinEquiv.symm a i).val)

/-- The complete fixed-alphabet row schedule: two endpoints followed by every
forward-table entry in increasing numeric label order. -/
def commands (q t : ℕ) : List (MachineProductRow.Command t) :=
  sourceCommand t :: targetCommand t :: (List.finRange (q ^ t)).map (imageCommand q t)

theorem commands_length (q t : ℕ) : (commands q t).length = q ^ t + 2 := by
  simp [commands]

end MaxCutGames.Explicit.ProductMachineSemantics

/-! Actual power-header emission by fixed-width Horner evaluation of
`[1,0,...,0]`, followed by physical transfer to the reverse accumulator. -/

namespace MaxCutGames.Explicit.MachineProductPower

open Turing
open MaxCutGames.Foundations.Complexity

variable {K Λ σ : Type} [DecidableEq K] {exponent : Nat}

def digits (i : Nat) : Nat := if i = 0 then 1 else 0

end MaxCutGames.Explicit.MachineProductPower

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineProductProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Explicit.MachineProductProgram

open Turing
open MaxCutGames.Foundations
open Complexity Hastad

abbrev Extra (t : Nat) := Fin 10 ⊕ Fin (t + 1)

end MaxCutGames.Explicit.MachineProductProgram

/-! Concrete header and initialized work-tape frames for the product machine. -/

/-! Three actual header reads for the fixed-alphabet, fixed-power product
machine. The constraint table stays in its original order on the formula tape. -/

/-! Actual literal initialization of the finitely many product power digits. -/

/-! The three actual output-header emissions of the product controller. -/

/-! Complete actual initialization of the independent-product machine. -/

/-! Polynomial bounds for actual field and row traces. The output accumulator
is excluded from local cleanup and is never rescanned by row emission. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSingleOrbitProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Physical postprocessing of the two-side address codec. The program reads
`2*C,q,m`, writes `C,q,m`, and replaces each row `u,C+v,table` by `u,v,table`.
Only the fixed alphabet size `q` occurs in finite control. All input-dependent
integers reside on unary tapes. Six Bool tapes suffice.
-/

namespace MaxCutGames.Explicit.MachineSingleOrbitProgram

open Turing
open MaxCutGames.Foundations.Complexity MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction

abbrev State := Unit × Option Bool

def initialState : State := ((), none)

end MaxCutGames.Explicit.MachineSingleOrbitProgram

/-! Exact streaming traces in the single-orbit postprocessor. -/

/-! Physical unary header conversion, with an exact TM2 transition count. -/

/-! Actual subtraction of the right-side address offset, preserving the unary
capacity tape for every later edge. -/

/-! The exact input/output codec of the one-orbit postprocessor. Doubling is
only an encoding adapter: no equality of game values under independent labels
on the two copies is asserted. -/

/-! Complete ordered row traversal of the physical one-orbit postprocessor. -/

namespace MaxCutGames.Explicit.MachineSingleOrbitRows

open Turing MaxCutGames.Foundations.Complexity
open MachineSingleOrbitProgram

theorem joinTrace {α : Type*} {f : α → α} {x y z : α} {m n : Nat}
    (h : f^[m] x = y) (h' : f^[n] y = z) : f^[n + m] x = z := by
  rw [Function.iterate_add_apply, h, h']

end MaxCutGames.Explicit.MachineSingleOrbitRows

/-! Actual tape cleanup, accumulator reversal, and halt for the one-orbit
postprocessor. The time bound is derived from an actual executed prefix. -/

/-!
Complete finite-machine postprocessing of the doubled address representation.
Every input field and row is physically processed. The time polynomial is in
the literal input bit length, including the final reversal and all tape cleanup.
-/

namespace MaxCutGames.Explicit.MachineSingleOrbitRuntime

open Turing MaxCutGames.Foundations.Complexity
open MachineSingleOrbitProgram
open MachineSingleOrbitRows

noncomputable section

def prefixPolynomial : Polynomial Nat :=
  Polynomial.X + (Polynomial.X + Polynomial.C 4) * Polynomial.X + Polynomial.C 2

end

end MaxCutGames.Explicit.MachineSingleOrbitRuntime

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionTableRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual execution of the subdivision controller's full-table reader.
The reader consumes exactly the fixed number of zero-delimited table entries,
retains the unread input suffix, and reverses the saved table into forward order.
No table entry is stored in finite control; only the number of delimiters is.
-/

namespace MaxCutGames.Explicit.MachineSubdivisionTableRead

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def tapes (base : Tape → List Bool) (input reversed : List Bool) : Tape → List Bool :=
  Function.update (Function.update base Tape.input input) Tape.permutationReverse reversed

@[simp] theorem tapes_input (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .input = input := by simp [tapes]

@[simp] theorem tapes_reverse (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .permutationReverse = reversed := by simp [tapes]

theorem update_input_inline_MachineSubdivisionTableRead (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .input replacement =
      tapes base replacement reversed := by
  funext k
  cases k <;> simp [tapes]

theorem update_reverse_inline_MachineSubdivisionTableRead (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .permutationReverse replacement =
      tapes base input replacement := by
  funext k
  cases k <;> simp [tapes]

def finalTapes (base : Tape → List Bool) (suffix bits : List Bool) : Tape → List Bool :=
  Function.update (tapes base suffix []) .permutation (bits ++ base .permutation)

@[simp] theorem finalTapes_input (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .input = suffix := by simp [finalTapes]

@[simp] theorem finalTapes_reverse (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .permutationReverse = [] := by simp [finalTapes]

@[simp] theorem finalTapes_permutation (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .permutation = bits ++ base .permutation := by simp [finalTapes]

end MaxCutGames.Explicit.MachineSubdivisionTableRead

/-!
One whole occurrence iteration of the actual subdivision controller.
The proved trace includes both endpoint loads, the dynamic full-table reader,
the four-row template, all three local drains, and private-index increments.
-/

namespace MaxCutGames.Explicit.MachineSubdivisionBody

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def incrementTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update base .middle (true :: base .middle))
      .first (true :: true :: base .first))
    .last (true :: true :: base .last)

theorem rowField_ne_scratch_inline_MachineSubdivisionBody (j : Fin 6) : rowField j ≠ Tape.copyScratch := by
  fin_cases j <;> decide

theorem rowField_ne_accumulator_inline_MachineSubdivisionBody (j : Fin 6) : rowField j ≠ Tape.accumulator := by
  fin_cases j <;> decide

end MaxCutGames.Explicit.MachineSubdivisionBody

/-! Concrete frames and literal row words for the subdivision occurrence loop. -/

/-! Exact tape framing, row serialization, and a uniform polynomial bound for
the already constructed whole subdivision-body execution. -/

/-! Complete physical occurrence traversal of the subdivision program. -/

namespace MaxCutGames.Explicit.MachineSubdivisionLoop

open Turing
open MaxCutGames.Foundations
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionProgram

def bodyBound (n q Q : Nat) : Nat := 100 * (n + 3 * Q + q * (q + 1) + 1)

end MaxCutGames.Explicit.MachineSubdivisionLoop

/-! Actual cleanup, output reversal, and polynomial finishing overhead. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineSubdivisionCorrespondence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual streamed bytes coincide with the numbered semantic subdivision.
The controller copies the last table unchanged, so its input contract explicitly
requires involutive tables; binary translations satisfy this condition. -/

/-! The complete finite subdivision machine, including its polynomial runtime
in the actual serialized input length and exact full-table output. -/

namespace MaxCutGames.Explicit.MachineSubdivisionRuntime

open Turing
open MaxCutGames.Foundations
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionProgram

noncomputable section

def prefixPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.X * (Polynomial.C 100 *
    (Polynomial.C 4 * Polynomial.X + Polynomial.C (q * (q + 1)) + 1) + 1) +
    Polynomial.C 62 * Polynomial.X + Polynomial.C (q + 50)

end
end MaxCutGames.Explicit.MachineSubdivisionRuntime

end OAI
end


