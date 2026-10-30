-- Prove2me | Definitions.Def_OAIQ081S089
-- name    : OAIQ081S089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:15:39.384609+00:00
-- url     : https://prove2.me/theorems/f85982df-82c7-46e3-9ea7-d1978c88938e
-- title:
--   Definitions bundle OAIQ081S089 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 102 declarations of OpenAI's Lean: 62 definitions and 40 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.pushed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problemAssignment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problemWeights`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problemX`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.lookupBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.metadataRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Literal.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Literal.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params.labelStream`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking.Spec.suffix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking.addressSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.Spec.addresses`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.Spec.encodeVertex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.Spec.metadata`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.addressRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.covered`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.entries`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.keys`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.records`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.factors`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Problem.words`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental.prefixOverlap`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope.rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope.values`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.reverse`, `OAI.Algorithms.SubexponentialSAT.Subexp.BucketProgram.scan`, `OAI.Algorithms.SubexponentialSAT.Subexp.BucketProgram.scanLoop`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.bucketCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.scanProgram`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.callback`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.program` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_ProgramStateFrames`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramEmit`, `SubexponentialSAT_SqrtLog_LayoutProducedHeadsScope`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankRun`, `SubexponentialSAT_SqrtLog_LayoutProgramFrontend`, `SubexponentialSAT_SqrtLog_LayoutProgramLiteral`, `SubexponentialSAT_SqrtLog_LayoutProgramNativePacking`, `SubexponentialSAT_SqrtLog_LayoutProgramPackLabels`, `SubexponentialSAT_SqrtLog_LayoutProgramScanRestore`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage`, `SubexponentialSAT_SqrtLog_PackingCallerProgramModel`, `SubexponentialSAT_SqrtLog_PackingHeadIncrementalSequential`, `SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_BucketProgram`, `SubexponentialSAT_Subexp_GatherProgram`, `SubexponentialSAT_Subexp_PackingAddressSemantics`, `SubexponentialSAT_Subexp_PackingBucketCalls`, `SubexponentialSAT_Subexp_PackingBucketTable`, `SubexponentialSAT_Subexp_PackingCanonicalData`, `SubexponentialSAT_Subexp_PackingExtractionSemantics`, `SubexponentialSAT_Subexp_PackingInverseStage`, `SubexponentialSAT_Subexp_PackingMetadata`, `SubexponentialSAT_Subexp_PackingPlumbing`, `SubexponentialSAT_Subexp_PackingVertexLabels`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_TupleProgram`, `SubexponentialSAT_Subexp_TypeEnumeration`, `SubexponentialSAT_Subexp_UniversalRowExecution`, `SubexponentialSAT_Subexp_UniversalRowFactorLoop`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S074` and `OAIQ081S075` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S108`, `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S111`, `OAIQ081S112`, `OAIQ081S113` and `OAIQ081S114`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.initializeLocal_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.prepareLocalInverse_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_head_max_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S074
import Definitions.Def_OAIQ081S075

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

theorem eval_liftCommand {r s R S : ℕ} {c : Cmd r s} {n : ℕ} {a b : State r s}
    (h : Eval c n a b) (inputStack outputStack : Fin s)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (frame : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack) :
    Eval (liftCommand c inputStack outputStack register stack) (n + 1)
      (embedState register stack frame a) (embedState register stack frame b) :=
  eval_call_lifted (compiled c inputStack outputStack) register stack frame hr hs
    (compiled_halt_trace h inputStack outputStack)

theorem eval_liftCommand_from_state {r s R S : ℕ}
    (c : Cmd r s) (inputStack outputStack : Fin s)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (d : State R S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {n : ℕ} {b : State r s} (h : Eval c n (projectState register stack d) b) :
    Eval (liftCommand c inputStack outputStack register stack) (n + 1)
      d (embedState register stack d b) := by
  simpa only [embedState_project register stack d hr hs] using
    eval_liftCommand h inputStack outputStack register stack d hr hs

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete extension-ring denominator program. It first lifts the actual
scalar-half word, then runs the paid native multiplication loop. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing
open IntegerRingLiftProgram

theorem budget_polynomial (R t d : ℕ) :
    budget R t d ≤ polynomialBudget R (baseWidth 3 t) d := by
  have hs := (modelSignedBudget_le_scaled (baseWidth 3 t) t d).trans
    (modelScaledBudget_polynomial (baseWidth 3 t) t d)
  have hm := HornerProgram.Services.mulBudget_polynomial (baseWidth 3 t) d
  unfold budget powerBudget polynomialBudget
  have hp := Nat.mul_le_mul (Nat.sub_le R 1)
    (Nat.add_le_add_right (Nat.add_le_add_right hm (8*(d*baseWidth 3 t))) 11)
  simp only [Nat.mul_assoc] at hs hp ⊢
  omega

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

/-- Reuse the same tuple storage after each Cartesian expansion. Two actual
stack transfers restore the forward serialized order. -/
abbrev expandStep : Cmd 10 9 :=
  .seq cartesianCmd
    (.seq (.call (StackRoutines.transferProgram 5 6 6 7))
      (.seq (.call (StackRoutines.transferProgram 6 0 6 7)) (pushConst 5 6 false)))

abbrev powerLoop : Cmd 10 9 := .while 9 (.seq expandStep readDepth)
abbrev powerCmd : Cmd 10 9 := .seq readDepth powerLoop

abbrev generateCmd : Cmd 10 9 := .seq initCmd powerCmd

/-- One finite instruction table for all alphabets and all tuple dimensions. -/
def generateProgram := StructuredCalls.compiled generateCmd 1 0

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BucketProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for one packing bucket

The input is a framed query followed by framed `(type key, vertex payload)`
records. The routine compares actual bit strings. It consumes all records,
keeps the query on port 2, and prepends matching framed payloads on port 5.
Supplying records in reverse vertex order produces the original bucket order.
-/

namespace SubexponentialSAT.Subexp.BucketProgram

open BitProgram StructuredProgram StructuredCalls SubexpRecordScan

abbrev scanLoop : StructuredCalls.Cmd 5 6 := .while 1 loopBody
abbrev scan : StructuredCalls.Cmd 5 6 := .seq peekInput scanLoop

end SubexponentialSAT.Subexp.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GatherProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program gathering runtime-selected rows

The packed assignment is on stack 0 and its unary row width on stack 3.
Stack 8 contains `ProgramEncoding.encodeRecords` of unary index words.
The program preserves the assignment and width and writes the selected rows,
in plan order, to stack 1. All widths and indices are stack data.
-/

namespace SubexponentialSAT.Subexp.GatherProgram

open BitProgram StackRoutines StructuredCalls

theorem callback_eval (earlier : List (List Bool)) (row rest width bits tail acc : List Bool)
    (hil : bits.length = earlier.length)
    (hrows : ∀ r ∈ earlier, r.length = width.length) (hr : row.length = width.length) :
    Eval callback (earlier.length * (14 * width.length + 10) + 18 * width.length + 20)
      (RecordPrograms.state ports (baseState (earlier.flatten ++ (row ++ rest)) width acc)
        false true false tail bits.reverse)
      (RecordPrograms.state ports
        (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
        false true false tail []) := by
  let a := RecordPrograms.state ports
    (baseState (earlier.flatten ++ (row ++ rest)) width acc) false true false tail bits.reverse
  let b : State 3 10 := ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩
  have hl := lookup_eval earlier row rest width bits.reverse a
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simpa using hil) hrows hr
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
    (by simp [a, ports, RecordPrograms.state, baseState])
  have ht := transfer_eval (1 : Fin 10) 9 (by decide) b.regs b.stacks
  have hfinal : (⟨readRegs b.regs 0 1 none, transferStacks 1 9 b.stacks⟩ : State 3 10) =
      RecordPrograms.state ports
        (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
        false false false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp [a, b, ports, RecordPrograms.state, baseState, readRegs]
    · funext j
      fin_cases j <;> simp [a, b, ports, RecordPrograms.state, baseState, transferStacks]
  rw [hfinal] at ht
  have hs : Eval (RecordPrograms.atom (.set (1 : Fin 3) true)) 1
      (RecordPrograms.state ports
        (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
        false false false tail [])
      (RecordPrograms.state ports
        (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
        false true false tail []) := by
    have he : (StructuredProgram.Atom.set (1 : Fin 3) true).eval
        (RecordPrograms.state ports
          (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
          false false false tail []) =
        RecordPrograms.state ports
          (baseState (earlier.flatten ++ (row ++ rest)) width (row.reverse ++ acc))
          false true false tail [] := by
      apply congrArg₂ StructuredProgram.State.mk
      · funext j
        fin_cases j <;> simp [ StructuredProgram.Atom.instr, execInstr,
          ports, RecordPrograms.state, baseState]
      · rfl
    rw [← he]
    exact .base (.atom _ _)
  have t := hl.seq (ht.seq hs)
  dsimp [callback]
  convert t using 1 ; simp [a, b, ports, RecordPrograms.state, baseState, hr] ; omega

theorem callback_index_eval (rows : List (List Bool)) (width bits tail acc : List Bool)
    (hi : bits.length < rows.length)
    (hrows : ∀ row ∈ rows, row.length = width.length) :
    Eval callback (bits.length * (14 * width.length + 10) + 18 * width.length + 20)
      (RecordPrograms.state ports (baseState rows.flatten width acc)
        false true false tail bits.reverse)
      (RecordPrograms.state ports
        (baseState rows.flatten width ((rows.getD bits.length []).reverse ++ acc))
        false true false tail []) := by
  have ht : ∀ row ∈ rows.take bits.length, row.length = width.length := by
    intro row hr
    exact hrows row (List.mem_of_mem_take hr)
  have hr : (rows.getD bits.length []).length = width.length := by
    rw [List.getD_eq_getElem rows [] hi]
    exact hrows _ (List.getElem_mem hi)
  have h := callback_eval (rows.take bits.length) (rows.getD bits.length [])
    (rows.drop (bits.length + 1)).flatten width bits tail acc
    (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]) ht hr
  simpa only [← row_decomposition rows bits.length hi,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)] using h

theorem callback_contract (rows : List (List Bool)) (width : List Bool)
    (hrows : ∀ row ∈ rows, row.length = width.length) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost width.length) (invariant rows width) (effect rows)
      (fun bits => bits.length < rows.length) := by
  intro bits tail base hi hinv
  obtain ⟨acc, rfl⟩ := hinv
  refine ⟨callbackCost width.length bits,
    baseState rows.flatten width ((rows.getD bits.length []).reverse ++ acc),
    le_rfl, ⟨_, rfl⟩, ?_, ?_⟩
  · simp [effect, baseState]
  · exact callback_index_eval rows width bits tail acc hi hrows

/-- Execution of the single fixed command. The only input hypotheses are
uniform row widths and validity of the runtime plan indices. -/
theorem command_eval (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ n, n + 1 ≤ traceCost rows width.length plan ∧
      Eval command n (inputState rows width plan) (outputState rows width plan) := by
  obtain ⟨n, next, hn, hnext, history, run⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost width.length) (invariant rows width)
    (effect rows) (fun bits => bits.length < rows.length)
    (callback_contract rows width hrows) (indexRecords plan) []
    (baseState rows.flatten width []) (indexRecords_valid rows plan hplan) ⟨[], rfl⟩
    false false false
  obtain ⟨acc, rfl⟩ := hnext
  have hacc : acc = (gathered rows plan).reverse := by
    have hh := history.fold_of_false (fun _ _ => rfl)
      (fun s => s.stacks 9)
      (fun out bits => (rows.getD bits.length []).reverse ++ out)
      (fun _ _ _ h => h)
    simpa only [baseState, ite_eq_left, ite_false, Fin.reduceEq, accumulator_fold,
      List.append_nil] using hh
  subst acc
  let middle := RecordPrograms.state ports
    (baseState rows.flatten width (gathered rows plan).reverse) false true false [] []
  have hrun : Eval (RecordPrograms.iterate ports callback) n
      (inputState rows width plan) middle := by
    simpa [inputState, middle, ProgramEncoding.encodeRecords, unread_false, any_false] using run
  have ht := transfer_eval (9 : Fin 10) 1 (by decide) middle.regs middle.stacks
  have hfinal : (⟨readRegs middle.regs 0 1 none,
      transferStacks 9 1 middle.stacks⟩ : State 3 10) = outputState rows width plan := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp [middle, ports, RecordPrograms.state, baseState, readRegs]
    · funext j
      fin_cases j <;> simp [middle, ports, RecordPrograms.state, baseState,
        transferStacks]
  have ht' : Eval (.call (transferProgram (9 : Fin 10) 1 (0 : Fin 3) 1))
      (3 * (gathered rows plan).length + 3) middle (outputState rows width plan) := by
    rw [hfinal] at ht
    simpa [middle, ports, RecordPrograms.state, baseState] using ht
  refine ⟨n + (3 * (gathered rows plan).length + 3), ?_, hrun.seq ht'⟩
  dsimp [traceCost]
  omega

/-- The full, halted trace of the generated finite instruction table. -/
theorem program_run (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    RunsIn program (traceCost rows width.length plan)
      ((inputState rows width plan).withPC (some program.entry))
      ((outputState rows width plan).withPC none) := by
  obtain ⟨n, hn, h⟩ := command_eval rows width plan hrows hplan
  exact ⟨n + 1, hn, StructuredCalls.compiled_halt_trace h 8 1⟩

end SubexponentialSAT.Subexp.GatherProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

abbrev selector : Program 8 9 (size SelectorProgram.command + 1) :=
  ProgramLinking.liftProgram SelectorProgram.program lowRegs lowStacks

abbrev callback : Cmd 8 9 :=
  .seq (.call (StackRoutines.copyProgram 7 0 4 (0 : Fin 8) 1))
    (.seq (.call selector)
      (.seq (.call (StackRoutines.clearProgram 0 (0 : Fin 8) 1))
        (.seq (.call (StackRoutines.clearProgram 2 (0 : Fin 8) 1))
          (.seq (TupleProgram.pushConst 8 0 false)
            (.seq (TupleProgram.escape emitPorts) (TupleProgram.pushConst 8 0 true))))))

abbrev command : Cmd 8 9 :=
  .seq (TupleProgram.pushConst 8 0 false) (RecordPrograms.iterate ports callback)

abbrev program : Program 8 9 (size command + 1) := compiled command 6 8

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingVertexLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Gathering the actual assignment type at every vertex before packing. -/

namespace SubexponentialSAT.Subexp.PackingVertexLabels

open BitProgram StructuredCalls MatrixProgramSupport

def state (regs : Fin 8 → Bool) (array output width plan source payload index records temp : List Bool) :
    Data :=
  ⟨regs, ![array, output, [], width, [], [], [], [], plan, [],
    source, payload, index, records, temp]⟩

theorem state_stacks (regs : Fin 8 → Bool)
    (array output width plan source payload index records temp : List Bool) (i : Fin 15) :
    (state regs array output width plan source payload index records temp).stacks i =
      if i = 0 then array else if i = 1 then output else if i = 3 then width
      else if i = 8 then plan else if i = 10 then source else if i = 11 then payload
      else if i = 12 then index else if i = 13 then records else if i = 14 then temp else [] := by
  fin_cases i <;> rfl

theorem state_of_stacks (d : Data) (regs : Fin 8 → Bool)
    (array output width plan source payload index records temp : List Bool)
    (h : d.stacks =
      (state regs array output width plan source payload index records temp).stacks) :
    d = state d.regs array output width plan source payload index records temp := by
  apply congrArg₂ StructuredProgram.State.mk rfl h

def setData (i : Fin 8) (b : Bool) (d : Data) : Data :=
  ⟨Function.update d.regs i b, d.stacks⟩

theorem set_eval (i : Fin 8) (b : Bool) (d : Data) :
    Eval (.base (.atom (.set i b))) 1 d (setData i b d) := by
  exact .base (.atom _ _)

theorem parser_state (regs : Fin 8 → Bool)
    (array output width plan source payload index records temp newSource newPayload : List Bool)
    (tag present found : Bool) :
    RecordPrograms.state ports
      (state regs array output width plan source payload index records temp)
      tag present found newSource newPayload =
    state (parserRegs regs tag present found)
      array output width plan newSource newPayload index records temp := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> simp [ ports, state]

/-- Lift the checked gather machine into the first ten work ports. -/
theorem gatherCall_eval (rows : List (List Bool)) (width : List Bool) (plan : List ℕ)
    (regs : Fin 8 → Bool) (source index records : List Bool)
    (h0 : regs 0 = false) (h1 : regs 1 = false) (h2 : regs 2 = false)
    (hrows : ∀ row ∈ rows, row.length = width.length)
    (hplan : ∀ i ∈ plan, i < rows.length) :
    ∃ n, n ≤ GatherProgram.traceCost rows width.length plan ∧
      Eval gatherCall n
        (state regs rows.flatten [] width (planBytes plan) source [] index records [])
        (state regs rows.flatten (GatherProgram.gathered rows plan) width [] source [] index records []) := by
  let a := state regs rows.flatten [] width (planBytes plan) source [] index records []
  let b := state regs rows.flatten (GatherProgram.gathered rows plan) width [] source [] index records []
  obtain ⟨n, hn, ht⟩ := GatherProgram.program_run rows width plan hrows hplan
  have ha : embedState gatherRegs gatherPorts a (GatherProgram.inputState rows width plan) = a := by
    apply SelectorMapProgram.embed_eq _ _ gatherRegs_injective gatherPorts_injective
    · intro i
      fin_cases i <;> simp [a, state, gatherRegs, GatherProgram.inputState,
        GatherProgram.baseState, RecordPrograms.state, GatherProgram.ports, h0, h1, h2]
    · intro i
      fin_cases i <;> simp [a, state, gatherPorts, GatherProgram.inputState,
        GatherProgram.baseState, RecordPrograms.state, GatherProgram.ports, planBytes]
    · intros; rfl
    · intros; rfl
  have hb : embedState gatherRegs gatherPorts a (GatherProgram.outputState rows width plan) = b := by
    apply SelectorMapProgram.embed_eq _ _ gatherRegs_injective gatherPorts_injective
    · intro i
      fin_cases i <;> simp [b, state, gatherRegs, GatherProgram.outputState, h0, h1, h2]
    · intro i
      fin_cases i <;> simp [b, state, gatherPorts, GatherProgram.outputState]
    · intros; rfl
    · intro i hi
      have hi1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      have hi8 : i ≠ 8 := fun h => hi ⟨8, h.symm⟩
      simp only [a, b, state_stacks, ite_eq_right hi1, ite_eq_right hi8]
  have he := eval_call_lifted GatherProgram.program gatherRegs gatherPorts a
    gatherRegs_injective gatherPorts_injective ht
  rw [ha, hb] at he
  exact ⟨n, hn, he⟩

theorem labelRecords_cons (rows : List (List Bool)) (plan : List ℕ)
    (plans : List (List ℕ)) (start : ℕ) :
    labelRecords rows (plan::plans) start =
      (GatherProgram.gathered rows plan, List.replicate start true) ::
        labelRecords rows plans (start+1) := by
  simp [labelRecords, List.range'_succ]

theorem rawRecords_append (a b : List BucketProgram.Record) :
    BucketProgram.encodeRecords (a++b) =
      BucketProgram.encodeRecords a ++ BucketProgram.encodeRecords b := by
  induction a with
  | nil => rfl
  | cons a rest ih =>
      rcases a with ⟨key,value⟩
      simp only [List.cons_append, BucketProgram.encodeRecords, ih, List.append_assoc]

theorem reversed_output_cons (rows : List (List Bool)) (plan : List ℕ)
    (plans : List (List ℕ)) (start : ℕ) (records : List Bool) :
    BucketProgram.encodeRecords (labelRecords rows plans (start+1)).reverse ++
        (Encoding.frame (GatherProgram.gathered rows plan) ++
          (Encoding.frame (List.replicate start true) ++ records)) =
      BucketProgram.encodeRecords (labelRecords rows (plan::plans) start).reverse ++ records := by
  rw [labelRecords_cons, List.reverse_cons, rawRecords_append]
  simp only [BucketProgram.encodeRecords, List.append_nil, List.append_assoc]

def base (rows : List (List Bool)) (width : List Bool) (regs : Fin 8 → Bool)
    (index : ℕ) (records : List Bool) : Data :=
  state regs rows.flatten [] width [] [] [] (List.replicate index true) records []

/-- The sum of actual callback bounds and actual outer-reader overheads.
The runtime counter increases, so its current value is included explicitly. -/
def iterationCost (width : ℕ) : List (List ℕ) → ℕ → ℕ
  | [], _ => 0
  | plan::plans, start =>
      6*(planPayload plan).length + callbackCost width (planBytes plan).length start + 7 +
        iterationCost width plans (start+1)

def traceCost (width : ℕ) (plans : List (List ℕ)) (start : ℕ) : ℕ :=
  4 + iterationCost width plans start

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber scan primitives. Original ambient IDs are compared as
unary strings; the emitted indices count positions in the actual plan stream. -/
namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 5 11

def data (regs : Fin 5 → Bool)
    (query master scan payload decoded work tmp index acc count out : List Bool) : Data :=
  ⟨regs,![query,master,scan,payload,decoded,work,tmp,index,acc,count,out]⟩

def cleared (d : Data) (src : Fin 11) : Data :=
  ⟨status d.regs false false,Function.update d.stacks src []⟩

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev pushed := @SubexponentialSAT.Subexp.TupleProgram.pushedState 5 11

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual universal-type enumeration

The byte list is the output of the fixed Cartesian-power program.  The
semantic list and its finite equivalences only name that same physical
order; they are not executable inputs to any program.
-/

namespace SubexponentialSAT.Subexp.TypeEnumeration

open MulticolorTypes
open CollisionProgram (encodeType registerWord)
open AssignmentAlphabetSemantics

def universalBytes (r Q Δ : ℕ) : List (List Bool) :=
  TupleProgram.powerRows (wordBytes r Q) (Δ + 1) [[]]

theorem universalBytes_nodup {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (universalBytes r Q Δ).Nodup := by
  obtain ⟨a, tail, he, hn, _⟩ := wordBytes_order hr Q
  change (TupleProgram.powerRows (wordBytes r Q) (Δ + 1) [[]]).Nodup
  rw [← he]
  exact SubexpTupleRefinement.powerRows_encoded_nodup (wordCode hr hQ) (a :: tail) hn (Δ + 1)

theorem universalBytes_encode_mem {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (u : UniversalType r Q Δ) : encodeType u ∈ universalBytes r Q Δ := by
  obtain ⟨a, tail, he, _, hf⟩ := wordBytes_order hr Q
  unfold universalBytes
  rw [← he]
  change encodeType u ∈
    TupleProgram.powerRows (List.map (wordCode hr hQ).block (a :: tail)) (Δ + 1) [[]]
  simpa only [encodeTuple_eq hr hQ, ofWords_registerWord] using
    SubexpTupleRefinement.encodeTuple_mem_powerRows (wordCode hr hQ)
      (a :: tail) hf (Δ + 1) (registerWord u)

theorem universalBytes_mem_encode {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (bits : List Bool) (hb : bits ∈ universalBytes r Q Δ) :
    ∃ u : UniversalType r Q Δ, encodeType u = bits := by
  obtain ⟨a, tail, he, _, _⟩ := wordBytes_order hr Q
  unfold universalBytes at hb
  rw [← he] at hb
  obtain ⟨v, _, hv⟩ := (SubexpTupleRefinement.mem_powerRows_encoded
    (wordCode hr hQ) (a :: tail) (Δ + 1) bits).mp hb
  exact ⟨ofWords v, (encodeTuple_eq hr hQ v).symm.trans hv⟩

theorem universalBytes_order {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    ∃ us : List (UniversalType r Q Δ), us.map encodeType = universalBytes r Q Δ ∧
      us.Nodup ∧ ∀ u, u ∈ us := by
  obtain ⟨us, he⟩ := list_lift encodeType (universalBytes r Q Δ)
    (universalBytes_mem_encode hr hQ)
  refine ⟨us, he, List.Nodup.of_map encodeType ?_, ?_⟩
  · rw [he]
    exact universalBytes_nodup hr hQ Δ
  · intro u
    have hu := universalBytes_encode_mem hr hQ u
    rw [← he, List.mem_map] at hu
    obtain ⟨v, hv, hve⟩ := hu
    exact CollisionProgram.encodeType_injective hve ▸ hv

/-- Proof-only names for the physical tuple order. -/
noncomputable def typeList {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    List (UniversalType r Q Δ) := Classical.choose (universalBytes_order hr hQ Δ)

theorem typeList_bytes {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (typeList hr hQ Δ).map encodeType = universalBytes r Q Δ :=
  (Classical.choose_spec (universalBytes_order hr hQ Δ)).1

theorem typeList_nodup {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (typeList hr hQ Δ).Nodup :=
  (Classical.choose_spec (universalBytes_order hr hQ Δ)).2.1

theorem mem_typeList {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q) (u : UniversalType r Q Δ) :
    u ∈ typeList hr hQ Δ :=
  (Classical.choose_spec (universalBytes_order hr hQ Δ)).2.2 u

@[simp] theorem universalBytes_length (r Q Δ : ℕ) :
    (universalBytes r Q Δ).length = blockSize r Q Δ := by
  unfold universalBytes
  rw [TupleProgram.generated_count, wordBytes_length]
  simp only [blockSize, pow_mul]

end SubexponentialSAT.Subexp.TypeEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

def coveredRecords (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) : List (List Bool × List Bool) :=
  (PackingReorder.packedVertices P).reverse.map (row P encodeVertex encodeType)

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical subroutine calls for the all-type packing fold. -/

namespace SubexponentialSAT.Subexp.PackingBucketCalls

open BitProgram StructuredCalls MatrixProgramSupport

def scanProgram := compiled BucketProgram.scan 0 5

abbrev bucketCall : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram scanProgram bucketRegs bucketPorts)

end SubexponentialSAT.Subexp.PackingBucketCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed all-key bucket/minimum controller. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

abbrev callback : Cmd 8 15 := sequence [
  MatrixProgramSupport.copy 6 0 12,
  bucketCall,
  MatrixProgramSupport.copy 5 9 12,
  countCall,
  minimumCall,
  move 14 10 12,
  transfer 2 9,
  emitFrame 9 5 12 (by decide),
  emitFrame 5 9 12 (by decide),
  TupleProgram.pushConst 9 0 true,
  transfer 9 11,
  .base (.atom (.set 5 false)),
  .base (.atom (.set 6 true)),
  .base (.atom (.set 7 false))]

abbrev command : Cmd 8 15 :=
  .seq (RecordPrograms.iterate ports callback)
    (.seq (TupleProgram.pushConst 11 0 false) (transfer 11 5))

def program := compiled command 7 5

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem clearMany_eval {S : ℕ} (ps : List (Fin S)) (a : Data S) :
    Eval (clearMany ps) (clearManyCost ps a) a (clearManyState ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip a)
  | cons p ps ih => exact .seq (clear_eval p a) (ih (clearState p a))

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

abbrev Code := Cmd 16 768

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentSeedRange
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ascending framed unary seed indices from a runtime unary seed count. -/

namespace SubexponentialSAT.Subexp.AssignmentSeedRange

open BitProgram StructuredCalls TupleProgram

abbrev reverse : Cmd 5 6 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks)

abbrev command : Cmd 5 6 := .seq (pushConst 3 0 false)
  (.seq dimensions (.seq (pushConst 5 0 false)
    (.seq reverse (.seq (.call (StackRoutines.clearProgram 1 0 1)) reset))))

def program := compiled command 0 5

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingHeadIncrementalSequential
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Heads-first sequential ABI for the incremental physical head scorer. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Sequential
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

def prefixOverlap (z : Word r Q) (fixed : List (Word r Q)) : ℕ :=
  (fixed.map (fun w => ∑ t : Fin Q, if z t = w t then 1 else 0)).sum

omit [NeZero r] in
@[simp] theorem prefixOverlap_reverse (z : Word r Q) (fixed : List (Word r Q)) :
    prefixOverlap z fixed.reverse = prefixOverlap z fixed := by
  simp [prefixOverlap]

end Sequential
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramAssemblyScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native-scope specialization of the fixed weighted packing selector. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SqrtLog.Packing

def values (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) (s : ℕ) (hs : 0 < s) (hr : 0 < r) :=
  selectedValues (PackingIncidenceInput.Semantics.owner scopes n mask hmask) (PackingIncidenceInput.Semantics.factor scopes n mask hmask)
    a tail (terms scopes n mask Q) (PackingIncidenceInput.Semantics.seedIndices n (PackingIncidenceInput.Semantics.factorCount scopes mask))
    (weights n s (PackingIncidenceInput.Semantics.nativeEntries scopes mask).length r (a::tail).length hs hr (by simp))

def rows (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hmask : mask.length ≤ n)
    {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q)) (s : ℕ) (hs : 0 < s) (hr : 0 < r) :=
  (values scopes n mask hmask a tail s hs hr).reverse.map ReadPlan.encodeWord

@[simp] theorem rows_length (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (hmask : mask.length ≤ n) {r Q : ℕ} (a : Word r Q) (tail : List (Word r Q))
    (s : ℕ) (hs : 0 < s) (hr : 0 < r) :
    (rows scopes n mask hmask a tail s hs hr).length=n+PackingIncidenceInput.Semantics.factorCount scopes mask := by
  simp [rows,values,selectedValues,assign_length,PackingIncidenceInput.Semantics.seedIndices,headsFirst_length]

end SubexponentialSAT.SqrtLog.PackingProgram.Assembly.Scope

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingPlumbing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Verified stack moves used between the fixed packing subroutines. -/

namespace SubexponentialSAT.Subexp.PackingPlumbing

open BitProgram StructuredCalls PackingProgramSupport

theorem Op.eval (op : Op) (a : Data) (h : op.Valid a) :
    Eval op.command (op.cost a) a (op.next a) := by
  cases op with
  | copy src dst tmp =>
    exact TupleProgram.copy_eval src dst tmp 0 1 h.1 h.2.1 h.2.2.1 (by decide) a h.2.2.2
  | transfer src dst =>
    exact TupleProgram.transfer_eval src dst 0 1 h (by decide) a
  | clear src => exact TupleProgram.clear_eval src 0 1 a
  | push dst bit => exact TupleProgram.pushConst_eval dst 0 bit a

theorem eval (ops : List Op) (a : Data) (h : Valid ops a) :
    Eval (command ops) (cost ops a) a (run ops a) := by
  induction ops generalizing a with
  | nil => exact Eval.base (.skip a)
  | cons op ops ih => exact (op.eval a h.1).seq (ih _ h.2)

end SubexponentialSAT.Subexp.PackingPlumbing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical label/type frontend for arbitrary runtime incidence plans.
The plans have already been produced by the native incidence scan. This
frontend gathers their actual words and generates the complete type alphabet;
it does not accept label records or block metadata as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.PackingProgramSupport

namespace Params

def labelStream (p : Params) : List Bool :=
  BucketProgram.encodeRecords (PackingVertexLabels.labelRecords p.rows p.planList 0).reverse

end Params

end SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingAddressSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The emitted storage-address table is the graph of the actual packed
coordinate order. Its lookups produce the existing reordering read plan. -/

namespace SubexponentialSAT.Subexp.PackingAddressSemantics

open ConstructivePacking

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem lookup_storageAddresses (P : PackingData V U) (encodeVertex : V → List Bool)
    (he : Function.Injective encodeVertex) (v : V) :
    (storageAddresses P encodeVertex).lookup (encodeVertex v) =
      some (List.replicate ((PackingReorder.storageVertices P).idxOf v) true) :=
  lookup_reverse_addressRows _ encodeVertex (storageVertices_nodup P) he v
    (PackingReorder.mem_storageVertices P v)

end SubexponentialSAT.Subexp.PackingAddressSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The records emitted by block extraction have the exact computed packing order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open ConstructivePacking MatrixProgramSupport

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem coverRows_typed (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) :
    coverRows (typedEntries P encodeVertex encodeType) P.blockCount 0 =
      (PackingReorder.packedVertices P).map (PackingMetadata.row P encodeVertex encodeType) := by
  unfold coverRows
  rw [← List.range_eq_range', ← List.map_coe_finRange]
  simp only [List.flatMap_map, blockRows, typedEntries, List.map_map,
    PackingReorder.packedVertices, List.map_flatMap]
  apply congrArg (fun f => (List.finRange P.blockCount).flatMap f)
  funext i
  apply List.map_congr_left
  intro u _
  simp only [Function.comp_apply]
  rw [entryVertex_typed]
  simp [PackingMetadata.row, PackingEntryEmitter.metadataPayload,
    GlobalBasisMetadata.Metadata.encode]

/-- The covered metadata bytes returned by the actual extraction trace. -/
theorem typed_extraction_metadata (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (c : Context) (hblock : c.block = []) :
    (advanceMany (typedEntries P encodeVertex encodeType) P.blockCount 0 c).metadata =
      SelectorProgram.rawRecords (PackingMetadata.coveredRecords P encodeVertex encodeType) ++
        c.metadata := by
  rw [advanceMany_metadata _ _ _ _ (by simpa [PackingMetadata.unary] using hblock), coverRows_typed]
  simp [PackingMetadata.coveredRecords, List.map_reverse]

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingInverseStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The inverse read plan is constructed by actual generated vertex queries
and actual scans of the emitted address table. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def inverseRows (records : List (List Bool × List Bool)) (D : ℕ) : List (List Bool) :=
  SelectorMapProgram.mappedRecords records (inverseQueries D)

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPackLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packing from physically produced label records. This route accepts the
incidence pair-gatherer's type labels directly, avoiding reconstruction of a
factor-to-incidence scope table. The fixed program computes blocks, uncovered
coordinates, metadata, storage order, and inverse addresses. It does not
assume any of those outputs. Label and universal-type byte production remain
explicit upstream obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace Spec

variable {U : Type*} [DecidableEq U]

def encodeVertex (s : Spec U) (v : Fin s.params.D) : List Bool := List.replicate v.val true

def metadata (s : Spec U) : List Bool :=
  SelectorProgram.rawRecords (PackingMetadata.records s.packing s.encodeVertex s.encodeType)

def addresses (s : Spec U) : List Bool :=
  SelectorProgram.rawRecords (PackingAddressSemantics.addressRows
    ((PackingReorder.storageVertices s.packing).map s.encodeVertex) 0).reverse

theorem encodeVertex_injective (s : Spec U) : Function.Injective s.encodeVertex := by
  intro v w h
  apply Fin.ext
  have hl := congrArg List.length h
  simpa [encodeVertex] using hl

end Spec

variable {U : Type*} [DecidableEq U]

def records (s : Spec U) : List BucketProgram.Record :=
  BucketProgram.vertexRecords s.packing.vertices.values s.packing.label s.encodeType s.encodeVertex

def keys (s : Spec U) : List (List Bool) := s.types.values.map s.encodeType

def entries (s : Spec U) : List PackingExtraction.Entry :=
  PackingExtraction.typedEntries s.packing s.encodeVertex s.encodeType

def covered (s : Spec U) : List (List Bool × List Bool) :=
  PackingMetadata.coveredRecords s.packing s.encodeVertex s.encodeType

def addressRecords (s : Spec U) : List (List Bool × List Bool) :=
  PackingAddressSemantics.storageAddresses s.packing s.encodeVertex

end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingCanonicalData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual assignment data used by canonical packing

The rows are the array emitted by the natural assignment program. Numeric
scope plans recover its actual type labels. The universal type enumeration
names the order of the physical tuple generator, without supplying a lookup
table or assuming the correctness of a packing result.
-/

namespace SubexponentialSAT.Subexp.PackingCanonicalSpec

open MulticolorTypes ConstructivePacking

variable {D r Q Δ : ℕ}

noncomputable def types (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    FiniteEnumeration (UniversalType r Q Δ) :=
  ⟨TypeEnumeration.typeList hr hQ Δ, TypeEnumeration.typeList_nodup hr hQ Δ,
    TypeEnumeration.mem_typeList hr hQ⟩

theorem types_bytes (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (types hr hQ Δ).values.map CollisionProgram.encodeType =
      TypeEnumeration.universalBytes r Q Δ :=
  TypeEnumeration.typeList_bytes hr hQ Δ

end SubexponentialSAT.Subexp.PackingCanonicalSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNativePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end physical packing from runtime word rows and native address
plans. Both labels and the full universal type list are generated before the
bucket/block/leftover controller runs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def Spec.suffix {U : Type*} [DecidableEq U] (s : Spec U) : PackLabels.Spec U :=
  ⟨s.params.base,s.types,s.label,s.encodeType,s.encodeType_injective⟩

noncomputable def addressSpec {D r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) : Spec (UniversalType r Q 1) where
  params := {
    D := D, Δ := 1, rows := words.map ReadPlan.encodeWord
    width := List.replicate (Q*r) true
    alphabet := AssignmentAlphabetSemantics.wordBytes r Q
    planList := labelPlans words address
    plans_count := by simp [labelPlans] }
  types := PackingCanonicalSpec.types hr hQ 1
  label := addressLabel words address
  encodeType := CollisionProgram.encodeType
  encodeType_injective := CollisionProgram.encodeType_injective
  rows_width := by
    intro row hrow
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hrow
    simp [ReadPlan.encodeWord_length,ReadPlan.wordWidth]
  plans_valid := labelPlans_valid words address
  label_records := addressLabel_records words address
  type_records := (PackingCanonicalSpec.types_bytes hr hQ 1).symm

end SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

namespace Problem

abbrev factors (p : Problem) := Semantics.factorCount p.scopes p.mask
def words (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  (PackingProgram.Assembly.Scope.values p.scopes p.n p.mask p.mask_le a tail p.s p.hs p.hr).reverse

theorem words_length (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.words a tail).length=p.n+p.factors := by
  have h := PackingProgram.Assembly.Scope.rows_length p.scopes p.n p.mask p.mask_le
    a tail p.s p.hs p.hr
  simpa [words,factors,PackingProgram.Assembly.Scope.rows] using h

noncomputable def spec (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    LayoutProgram.NativePacking.Spec (UniversalType p.r p.Q 1) :=
  LayoutProgram.NativePacking.addressSpec p.hr p.hQ (p.words a tail)
    (Address.address p.scopes p.n p.mask p.mask_le (p.words a tail) (p.words_length a tail))

@[simp] theorem spec_dimension (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.D=p.incidences := rfl
@[simp] theorem spec_depth (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.Δ=1 := rfl
@[simp] theorem spec_width (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.width=List.replicate (p.Q*p.r) true := rfl
@[simp] theorem spec_alphabet (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.alphabet=AssignmentAlphabetSemantics.wordBytes p.r p.Q := rfl
@[simp] theorem spec_rows (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.rows=(p.words a tail).map ReadPlan.encodeWord := rfl

end Problem

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeadsScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native scope selector has precisely the rational weights required by
the correlated-packing proof. All lists here are the actual producer lists. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes PackingProgram
open PackingProgram.Assembly

def problemX (p : PackingCallerProgram.Problem) : ℚ :=
  (1/(p.s:ℚ))*p.incidences/(Fintype.card (UniversalType p.r p.Q 1):ℚ)

def problemWeights (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) : Weights :=
  Scope.weights p.n p.s p.incidences p.r (a::tail).length p.hs p.hr (by simp)

def problemAssignment (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  Packing.computedWords
    (PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le)
    (PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le)
    a tail (Scope.terms p.scopes p.n p.mask p.Q)
    (PackingIncidenceInput.Semantics.seedIndices p.n p.factors)
    (problemX p) ((p.n:ℚ)/(2*(p.r:ℚ)))

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScanRestore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The old classifier parks the unary Q word on33. This wrapper physically
returns that word to22 and exposes only the two new counters and flag. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram

abbrev Data := State 10 64

end SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native entry of the all-incidence integer matrix. The actual packing
metadata is read twice; no precomputed integer matrix is supplied. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

variable {r Q D : ℕ}

def metadataRecords (P : PackingData (Fin D) (UniversalType r Q 1)) :=
  PackingMetadata.records P (fun v => List.replicate v.val true) CollisionProgram.encodeType

def lookupBudget (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D) : ℕ :=
  400*(GlobalBasisMetadata.volume (metadataRecords P) (List.replicate row.val true))^2+
  400*(GlobalBasisMetadata.volume (metadataRecords P) (List.replicate col.val true))^2+1

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLiteral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid preserving conversion of one scalar word into a complete forward
postfix literal. This is used for uncovered identity entries and zero branches. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Literal

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 3 4

def state (regs : Fin 3 → Bool) (payload out work result : List Bool) : Data :=
  ⟨regs,![payload,out,work,result]⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.Literal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word pushWord operator operators popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan )

local infixr:60 " ;; " => Cmd.seq

abbrev productBody : Cmd 3 8 := scan factorBody ;; emitLiteral 2 ;; drain 6 true

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactorLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Word)

abbrev equality : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram equalityProgram equalityRegs equalityStacks)

abbrev compareIndex : Cmd 8 32 :=
  .seq (.call (copyProgram 9 1 15 (0 : Fin 8) 1))
    (.seq (.call (copyProgram 16 12 15 (0 : Fin 8) 1))
      (.seq equality (RecordPrograms.atom (.pop 11 4 1))))

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end


