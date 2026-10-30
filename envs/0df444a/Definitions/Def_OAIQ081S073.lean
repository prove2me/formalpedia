-- Prove2me | Definitions.Def_OAIQ081S073
-- name    : OAIQ081S073
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:57:06.182264+00:00
-- url     : https://prove2.me/theorems/5858a9a0-0b91-406e-8ab1-1656d8907fc2
-- title:
--   Definitions bundle OAIQ081S073 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 82 definitions and 17 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.MetadataBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Guard.guardInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.lengthBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.action`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.sequence`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.numeratorCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.numeratorFold`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.numeratorPrepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.numeratorProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.cachePlainEmit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.cacheSignedEmit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.emitCached`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.emitSigned`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.computedWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.headSupport`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.numberedScoreTerm`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.scoreOffset`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.scoreTerm`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.naturalTerm`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.numberedTerm`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.numerator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.selectedValues`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.sequentialNumerator`, `OAI.Algorithms.SubexponentialSAT.Subexp.BucketProgram.loopBody`, `OAI.Algorithms.SubexponentialSAT.Subexp.GatherProgram.command` and 42 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCache`, `SubexponentialSAT_SqrtLog_LayoutProgramGuard`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry`, `SubexponentialSAT_SqrtLog_LayoutProgramLabels`, `SubexponentialSAT_SqrtLog_LayoutProgramNumeratorRun`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarStep`, `SubexponentialSAT_SqrtLog_LayoutProgramScan`, `SubexponentialSAT_SqrtLog_LayoutProgramScanRestore`, `SubexponentialSAT_SqrtLog_LayoutProgramStaging`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic`, `SubexponentialSAT_SqrtLog_PackingAlgorithm`, `SubexponentialSAT_SqrtLog_PackingProgramController`, `SubexponentialSAT_SqrtLog_PackingProgramCounts`, `SubexponentialSAT_SqrtLog_PackingProgramScores`, `SubexponentialSAT_SqrtLog_PackingSelection`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_Subexp_AssignmentAlphabetSemantics`, `SubexponentialSAT_Subexp_BucketProgram`, `SubexponentialSAT_Subexp_GatherProgram`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_MatrixEntryProgram`, `SubexponentialSAT_Subexp_MatrixPositionCountProgram`, `SubexponentialSAT_Subexp_MatrixProgramSupport`, `SubexponentialSAT_Subexp_MatrixScanProgram`, `SubexponentialSAT_Subexp_MatrixScanStepProgram`, `SubexponentialSAT_Subexp_PackingAddressSemantics`, `SubexponentialSAT_Subexp_PackingExtractionSemantics`, `SubexponentialSAT_Subexp_PackingInverseStage`, `SubexponentialSAT_Subexp_PackingMetadata`, `SubexponentialSAT_Subexp_PackingPlumbing`, `SubexponentialSAT_Subexp_PackingVertexLabels`, `SubexponentialSAT_Subexp_SelectorOutput`, `SubexponentialSAT_Subexp_TensorSpectrum`, `SubexponentialSAT_Subexp_TupleProgram`, `SubexponentialSAT_Subexp_TypeEnumeration`, `SubexponentialSAT_Subexp_UniversalTypeProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055` and `OAIQ081S056` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S090`, `OAIQ081S091`, `OAIQ081S093`, `OAIQ081S095`, `OAIQ081S096`, `OAIQ081S097` and `OAIQ081S099`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanStepProgram.command_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarProgram_runsIn_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Scan.scanStage_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S049
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S054
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S056

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

abbrev command : Cmd 3 10 :=
  .seq (RecordPrograms.iterate ports callback)
    (.call (transferProgram (9 : Fin 10) 1 (0 : Fin 3) 1))

abbrev program : Program 3 10 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 8 1

theorem embed_lookup_input (a : State 3 10) :
    embedState id lookupPort a ⟨a.regs, a.stacks ∘ lookupPort⟩ = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    exact embedState_register id lookupPort a _ Function.injective_id j
  · funext j
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      have hi : lookupPort i = j := Fin.ext rfl
      rw [← hi]
      exact embedState_stack id lookupPort a _ lookupPort_injective i
    · exact embedState_stack_frame id lookupPort a _ j (by
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        exact hj (hv ▸ i.isLt))

theorem embed_lookup_output (a : State 3 10) (row : List Bool) :
    embedState id lookupPort a
      ⟨readRegs a.regs 0 1 none, ArrayUpdatePrograms.readStacks row (a.stacks ∘ lookupPort)⟩ =
      ⟨readRegs a.regs 0 1 none,
        Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext j
    exact embedState_register id lookupPort a _ Function.injective_id j
  · funext j
    by_cases hj : j.val < 8
    · let i : Fin 8 := ⟨j.val, hj⟩
      have hi : lookupPort i = j := Fin.ext rfl
      rw [← hi, lookupPort_injective.extend_apply]
      clear hi
      clear_value i
      clear hj j
      fin_cases i <;> simp [ArrayUpdatePrograms.readStacks, lookupPort]
    · rw [Function.extend_apply' _ _ _ (by
        rintro ⟨i, hi⟩
        have hv := congrArg Fin.val hi
        exact hj (hv ▸ i.isLt))]
      have h1 : j ≠ 1 := by intro h; subst j; norm_num at hj
      have h2 : j ≠ 2 := by intro h; subst j; norm_num at hj
      simp [h1, h2]

theorem lookup_eval (earlier : List (List Bool)) (row rest width index : List Bool)
    (a : State 3 10)
    (ha : a.stacks 0 = earlier.flatten ++ (row ++ rest))
    (hw : a.stacks 3 = width) (hi : a.stacks 2 = index)
    (hil : index.length = earlier.length)
    (hrows : ∀ r ∈ earlier, r.length = width.length) (hr : row.length = width.length)
    (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) :
    Eval lookup (earlier.length * (14 * width.length + 10) + 15 * width.length + 16) a
      ⟨readRegs a.regs 0 1 none,
        Function.update (Function.update a.stacks 2 []) 1 (row ++ a.stacks 1)⟩ := by
  have t := ArrayUpdatePrograms.readProgram_trace (0 : Fin 3) 1 (by decide)
    earlier row rest width index a.regs (a.stacks ∘ lookupPort)
    ha hw hi hil hrows hr h4 h5 h6 h7
  have h := eval_call_lifted (ArrayUpdatePrograms.readProgram (0 : Fin 3) 1)
    id lookupPort a Function.injective_id lookupPort_injective
    (a := ⟨a.regs, a.stacks ∘ lookupPort⟩)
    (b := ⟨readRegs a.regs 0 1 none,
      ArrayUpdatePrograms.readStacks row (a.stacks ∘ lookupPort)⟩) t
  simpa only [embed_lookup_input, embed_lookup_output, lookup] using h

def invariant (rows : List (List Bool)) (width : List Bool) (a : State 3 10) : Prop :=
  ∃ acc, a = baseState rows.flatten width acc

end SubexponentialSAT.Subexp.GatherProgram

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

def stepCost (rows alphabet : Records) : ℕ :=
  expansionCost rows alphabet +
    6 * (ProgramEncoding.encodeRecords (cartesianOutput rows alphabet)).length + 8

abbrev powerCost (alphabet : Records) : ℕ → Records → ℕ
  | 0, _ => 2
  | n + 1, rows => stepCost rows alphabet + powerCost alphabet n (cartesianOutput rows alphabet) + 2

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

theorem readFrame_eval (src dst : Fin s) (h : src ≠ dst)
    (d : Data s) (bits tail : List Bool)
    (hsource : d.stacks src = Encoding.frame bits ++ tail) (hempty : d.stacks dst = []) :
    ∃ e, Eval (readFrame src dst h) (6 * bits.length + 4) d e ∧
      e.stacks = Function.update (Function.update d.stacks src tail) dst bits.reverse := by
  let p := fieldPorts src dst h
  let e := RecordPrograms.state p d false true (d.regs 2) tail bits.reverse
  have hs : RecordPrograms.state p d (d.regs 0) (d.regs 1) (d.regs 2)
      (Encoding.frame bits ++ tail) [] = d :=
    RecordPrograms.state_eq_self p d _ _ _ _ _ rfl rfl rfl hsource hempty
  have he := RecordPrograms.reader_eval p d bits tail [] (d.regs 0) (d.regs 1) (d.regs 2)
  rw [hs] at he
  refine ⟨e, ?_, rfl⟩
  simpa only [List.append_nil] using he

/-- Decode one frame and restore its little-endian order. -/
theorem readWord_eval (src dst tmp : Fin s) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (htd : tmp ≠ dst) (d : Data s) (bits tail : List Bool)
    (hs : d.stacks src = Encoding.frame bits ++ tail)
    (hd : d.stacks dst = []) (ht : d.stacks tmp = []) :
    ∃ e, Eval (readWord src dst tmp hst) (9 * bits.length + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks src tail) dst bits := by
  obtain ⟨a, ha, hsa⟩ := readFrame_eval src tmp hst d bits tail hs ht
  obtain ⟨b, hb, hsb⟩ := transfer_eval tmp dst htd a
  have hat : a.stacks tmp = bits.reverse := by rw [hsa]; simp
  have hatlen : (a.stacks tmp).length = bits.length := by
    rw [hat, List.length_reverse]
  refine ⟨b, ?_, ?_⟩
  · have hc := Eval.seq ha hb
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · rw [hsb, hsa]
    funext j
    by_cases hjd : j = dst
    · subst j
      simp [StackRoutines.transferStacks, hd, Ne.symm hsd, Ne.symm htd]
    · by_cases hjs : j = src
      · subst j
        simp [StackRoutines.transferStacks, hsd, hst, Ne.symm htd]
      · by_cases hjt : j = tmp
        · subst j
          simp [StackRoutines.transferStacks, hd, ht, Ne.symm hsd,
            Ne.symm hst, htd, Ne.symm htd]
        · simp [StackRoutines.transferStacks, hjd, hjs, hjt]

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixPositionCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical active-position step for a normalized matrix entry.
Stack 2 counts unchanged nonfixed pairs, stack 3 counts swapped nonfixed
pairs, and register 7 records compatibility of all positions seen so far. -/

namespace SubexponentialSAT.Subexp.MatrixPositionCountProgram

open BitProgram StructuredCalls StackRoutines MatrixPositionProgram

abbrev branch : Cmd 8 17 :=
  .ite 6 (.ite 4 (.base .skip) (TupleProgram.pushConst 2 0 true))
    (.ite 4 (TupleProgram.pushConst 3 0 true) (.base (.atom (.set 7 false))))

abbrev command : Cmd 8 17 :=
  .seq (comparePair false) (.seq (popResult 6) (.seq (comparePair true)
    (.seq (popResult 4) (.seq branch reset))))

abbrev program : Program 8 17 (size command + 1) := compiled command 13 2

end SubexponentialSAT.Subexp.MatrixPositionCountProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanStepProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One physical scan iteration: read four equal-width color records,
classify their same/swapped relation, and clear the consumed color buffers. -/

namespace SubexponentialSAT.Subexp.MatrixScanStepProgram

open BitProgram StructuredCalls StackRoutines

abbrev classify : Cmd 8 23 := .call
  (ProgramLinking.liftProgram MatrixPositionCountProgram.program id lowPorts)

abbrev command : Cmd 8 23 :=
  .seq MatrixColorReadProgram.pullFour (.seq classify clearWords)

end SubexponentialSAT.Subexp.MatrixScanStepProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite loop that scans the four color streams. Its loop count and
color width are runtime stacks. The result is specified by a finite fold of
the already proved physical scan step. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

abbrev body : Cmd 8 23 := .seq MatrixScanStepProgram.command popCount
abbrev loop : Cmd 8 23 := .while 6 body
abbrev command : Cmd 8 23 := .seq popCount loop

def program := compiled command 17 2

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete fixed control table for a joint-matrix entry.
All numerical parameters are runtime data. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

def scanStage : Code := series [
  copy 22 33,
  callLow MatrixInputProgram.program (by decide),
  callLow MatrixScanProgram.program (by decide)]

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual type-byte extractor and color classifier with arbitrary retained
integer caches. No finite-field arithmetic is called by this stage. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Scan

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.MatrixEntryProgram

variable {r Q Δ : ℕ}

def scanInput (i : Fin Δ) (u y : UniversalType r Q Δ)
    (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 9 → Bool) : Data :=
  input regs (List.replicate r true) (List.replicate Q true)
    (CollisionProgram.encodeType u) (CollisionProgram.encodeType y)
    (List.replicate (i.val+1) true) (List.replicate (Q*r) true)
    cache0 cache1 cache2 cache3

end SubexponentialSAT.SqrtLog.LayoutProgram.Scan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid joint-membership guard on actual type bytes. The four integer cache
words are arbitrary retained bytes; no finite-field numerator is invoked. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Guard

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.Subexp.MatrixWordEncoding SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q Δ : ℕ}

def guardInput (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ)
    (cache0 cache1 cache2 cache3 : List Bool) (regs : Fin 10 → Bool) : Data :=
  ⟨regs, fun j => if h : j.val < 37 then
    (Scan.scanInput i u y cache0 cache1 cache2 cache3
      (fun k => regs (k.castAdd 1))).stacks ⟨j.val,h⟩
    else if j = 37 then List.replicate t.val true else []⟩


end SubexponentialSAT.SqrtLog.LayoutProgram.Guard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev multiply : Cmd 8 18 := workCall (streamOperation true)

abbrev accumulate : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram (compiled (streamOperation false) 0 1) id sumPorts)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single cached scalar term: three parsed operands, three real signed
multiplications, and one real signed addition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev termStep : Cmd 8 18 :=
  .seq initializeOne (.seq multiply (.seq parse (.seq multiply
    (.seq parse (.seq multiply accumulate)))))

abbrev scalarCommand : Cmd 8 18 :=
  .seq parse (.while 7 (.seq termStep parse))

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open scoped BigOperators

def scalarProgram := compiled scalarCommand 0 16

open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def emitCached (which : Fin 3) : Code :=
  liftCommand LayoutScalarEmitter.emitPair 0 2 workRegisters (emitPorts which)

def emitSigned : Code := .ite 8 (emitCached 1) (emitCached 0)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

def cacheSignedEmit : Code := .seq emitSigned clearWork

def cachePlainEmit : Code := .seq (emitCached 0) clearWork

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramBody.lean

/-! A fixed, paid iteration producing the three real scalar operands. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def body : Code := .seq popH (.seq (readCached false) (.seq cacheSignedEmit
  (.seq (emitCached 2) (.seq (readCached true) (.seq cachePlainEmit advance)))))

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramLoop.lean

/-! The native unary loop produces all triples in increasing binomial index. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
def loop : Code := .seq popCount (.while 7 (.seq body popCount))

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramFinish.lean

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def prepare : Code := .seq initializeTriples (.seq loop (.seq finish clearIndex))
def prepareProgram := compiled prepare 7 18

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgram.lean

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete cached scalar call preserves both arrays, the width and the
clearing power. It constructs its operand stream and performs every signed
arithmetic operation on the primitive machine. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

abbrev numeratorPrepare : Cmd 9 25 :=
  .call (ProgramLinking.liftProgram prepareProgram id numeratorPreparePorts)
abbrev numeratorFold : Cmd 9 25 :=
  .call (ProgramLinking.liftProgram scalarProgram numeratorScalarRegisters numeratorScalarPorts)
abbrev numeratorCommand : Cmd 9 25 := .seq numeratorPrepare numeratorFold
def numeratorProgram := compiled numeratorCommand 7 23

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

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

abbrev scan : Cmd 10 64 := liftCommand scanStage 23 0 scanRegisters scanPorts
abbrev command : Cmd 10 64 := .seq scan restore

end SubexponentialSAT.SqrtLog.LayoutProgram.ScanRestore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumeratorRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
open MatrixScanProgram MatrixEntryEvaluation MatrixEntryKernel MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

def budget (A R W P : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) : ℕ :=
  guardStageCost r Q 1 0 t.val + MatrixEntryProgram.scanStageCost r Q 1 0 + 3*Q +
  LayoutProgramScalar.FromCounts.totalCost A R (unchangedCount (rows 0 u y)-1)
    (transposedCount (rows 0 u y)) W P +
  2*unchangedCount (rows 0 u y)+2*transposedCount (rows 0 u y)+20

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal integer universal constraints from the actual numerator program.
The outer anchor test also suppresses the clearing diagonal outside the joint. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram MatrixExtendedEntryProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

def value (A R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) : ℤ :=
  if anchorValid (0 : Fin 1) t u y then
    (if u=y then (2:ℤ)^(R-1) else 0)-LayoutCoefficientAlgorithm.scalarEntry (0:Fin 1) t A R u y
  else 0

def lengthBound (R W P : ℕ) (u y : UniversalType r Q 1) : ℕ :=
  (R-(MatrixScanProgram.unchangedCount (MatrixEntryEvaluation.rows 0 u y)-1))*
    LayoutProgramScalar.termGrowth (2*W+P)

def budget (A R W P D : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) : ℕ :=
  guardStageCost r Q 1 0 t.val+Numerator.budget A R W P t u y+
    27*CollisionProgram.typeWidth r Q 1+9*lengthBound R W P u y+
    100*(lengthBound R W P u y+D+1)^2+60

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The output boundary for the fixed first-match selector. A matching payload
is parsed onto the output port; an absent key copies the original query. -/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev materialize : Cmd 5 6 :=
  .ite 4 (.call (parseFrame 5 1))
    (.call (StackRoutines.copyProgram 2 1 4 (0 : Fin 5) 1))

abbrev command : Cmd 5 6 :=
  .seq (atom (.set 4 false)) (.seq peek (.seq scan materialize))

abbrev program : Program 5 6 (size command + 1) := compiled command 0 1

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls SubexpScanPrimitives


def selector : Code :=
  .call (ProgramLinking.liftProgram SelectorProgram.program id selectorPort)

def command : Code := .seq load (.seq selector (.seq cleanup parse))

def program := compiled command 0 2

end SubexponentialSAT.Subexp.GlobalBasisMetadata

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

def row (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) (v : V) : List Bool × List Bool :=
  (encodeVertex v, (value P encodeType v).encode)

/-- The actual emitter prepends pairs while traversing storage order. -/
def records (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) : List (List Bool × List Bool) :=
  (PackingReorder.storageVertices P).reverse.map (row P encodeVertex encodeType)

end SubexponentialSAT.Subexp.PackingMetadata

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

/-- This is the reversed table retained by the physical emitter. -/
def storageAddresses (P : PackingData V U) (encodeVertex : V → List Bool) :
    List (List Bool × List Bool) :=
  (addressRows ((PackingReorder.storageVertices P).map encodeVertex) 0).reverse

end SubexponentialSAT.Subexp.PackingAddressSemantics

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

def Op.command : Op → Cmd 16 48
  | .copy src dst tmp => PackingProgramSupport.copy src dst tmp
  | .transfer src dst => PackingProgramSupport.transfer src dst
  | .clear src => PackingProgramSupport.clear src
  | .push dst bit => TupleProgram.pushConst dst 0 bit

def Op.next : Op → Data → Data
  | .copy src dst _, a =>
      ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩
  | .transfer src dst, a =>
      ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks src dst a.stacks⟩
  | .clear src, a =>
      ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks src a.stacks⟩
  | .push dst bit, a => TupleProgram.pushedState dst 0 bit a

def Op.cost : Op → Data → ℕ
  | .copy src _ _, a => 7 * (a.stacks src).length + 5
  | .transfer src _, a => 3 * (a.stacks src).length + 3
  | .clear src, a => 2 * (a.stacks src).length + 3
  | .push _ _, _ => 2

def Op.Valid : Op → Data → Prop
  | .copy src dst tmp, a => src ≠ dst ∧ src ≠ tmp ∧ tmp ≠ dst ∧ a.stacks tmp = []
  | .transfer src dst, _ => src ≠ dst
  | .clear _, _ => True
  | .push _ _, _ => True

def command : List Op → Cmd 16 48
  | [] => .base .skip
  | op :: ops => .seq op.command (command ops)

def run : List Op → Data → Data
  | [], a => a
  | op :: ops, a => run ops (op.next a)

def cost : List Op → Data → ℕ
  | [], _ => 0
  | op :: ops, a => op.cost a + cost ops (op.next a)

def Valid : List Op → Data → Prop
  | [], _ => True
  | op :: ops, a => op.Valid a ∧ Valid ops (op.next a)

end SubexponentialSAT.Subexp.PackingPlumbing

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

abbrev loopBody : StructuredCalls.Cmd 5 6 := .seq oneRecord peekInput

end SubexponentialSAT.Subexp.BucketProgram

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

abbrev gatherCall : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram GatherProgram.program gatherRegs gatherPorts)

abbrev callback : Cmd 8 15 := sequence [
  transfer 11 14,
  readWord 14 8 2 (by decide),
  .base (.atom (.set 0 false)),
  .base (.atom (.set 1 false)),
  .base (.atom (.set 2 false)),
  gatherCall,
  MatrixProgramSupport.copy 12 14 2,
  emitFrame 14 13 2 (by decide),
  emitFrame 1 13 2 (by decide),
  TupleProgram.pushConst 12 0 true,
  .base (.atom (.set 5 false)),
  .base (.atom (.set 6 true)),
  .base (.atom (.set 7 false))]

abbrev command : Cmd 8 15 := RecordPrograms.iterate ports callback
def program := compiled command 10 13

end SubexponentialSAT.Subexp.PackingVertexLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentAlphabetSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual tuple-generator order is retained in the initializer alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

open OneHotAlphabetProgram MulticolorTypes

theorem encodeWord_injective {r Q : ℕ} (hr : 0 < r) :
    Function.Injective (@ReadPlan.encodeWord r Q) := by
  intro a b h
  apply SubexpTupleRefinement.encodeTuple_injective (colorCode hr) Q
  simpa only [encodeTuple_eq hr] using h

theorem wordBytes_encode_mem {r Q : ℕ} (hr : 0 < r) (w : Word r Q) :
    ReadPlan.encodeWord w ∈ wordBytes r Q := by
  rw [wordBytes, rows_eq_alphabet]
  rw [← encodeTuple_eq hr]
  exact SubexpTupleRefinement.encodeTuple_mem_powerRows (colorCode hr)
    (List.finRange r).reverse (by intro c; simp) Q w

theorem wordBytes_mem_encode {r Q : ℕ} (hr : 0 < r) (bits : List Bool)
    (h : bits ∈ wordBytes r Q) : ∃ w : Word r Q, ReadPlan.encodeWord w = bits := by
  rw [wordBytes, rows_eq_alphabet] at h
  obtain ⟨w, _, hw⟩ := (SubexpTupleRefinement.mem_powerRows_encoded (colorCode hr)
    (List.finRange r).reverse Q bits).mp h
  exact ⟨w, (encodeTuple_eq hr w).symm.trans hw⟩

/-- The proof-only word list follows the actual emitted byte order. The
program never receives this list or any semantic function as input. -/
theorem wordBytes_order {r : ℕ} (hr : 0 < r) (Q : ℕ) :
    ∃ a : Word r Q, ∃ tail : List (Word r Q),
      (a :: tail).map ReadPlan.encodeWord = wordBytes r Q ∧
      (a :: tail).Nodup ∧ ∀ w, w ∈ a :: tail := by
  obtain ⟨ws, hws⟩ := list_lift ReadPlan.encodeWord (wordBytes r Q)
    (wordBytes_mem_encode hr)
  have hnodup : ws.Nodup := List.Nodup.of_map ReadPlan.encodeWord
    (by rw [hws]; exact wordBytes_nodup hr Q)
  have hfull : ∀ w : Word r Q, w ∈ ws := by
    intro w
    have hw := wordBytes_encode_mem hr w
    rw [← hws, List.mem_map] at hw
    obtain ⟨u, hu, he⟩ := hw
    exact (encodeWord_injective hr he) ▸ hu
  cases ws with
  | nil =>
      have h := hfull (fun _ => ⟨0, hr⟩)
      simp at h
  | cons a tail => exact ⟨a, tail, hws, hnodup, hfull⟩

end SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def wordCode {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) : StackEncoding.BlockCode (Word r Q) where
  width := Q * r
  width_pos := Nat.mul_pos hQ hr
  block := ReadPlan.encodeWord
  length_block := ReadPlan.encodeWord_length
  injective_block := encodeWord_injective hr

theorem encodeTuple_eq {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (v : Fin (Δ + 1) → Word r Q) :
    SubexpTupleRefinement.encodeTuple (wordCode hr hQ) v = encodeType (ofWords v) := by
  rw [ReadPlan.encodeType_eq_words, registerWord_ofWords]
  rw [SubexpTupleRefinement.encodeTuple, StackEncoding.encodeDataStack_eq_flatMap]
  rw [List.flatMap_def, List.map_ofFn]
  rfl

end SubexponentialSAT.Subexp.TypeEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalTypeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual universal-type generation from the saved word alphabet and unary
slot count. The extra head coordinate is installed by one real push. -/

namespace SubexponentialSAT.Subexp.UniversalTypeProgram

open BitProgram StructuredCalls TupleProgram

def budget (alphabet : Records) (slots : ℕ) : ℕ :=
  powerCost alphabet (slots + 1) [[]] + 12

end SubexponentialSAT.Subexp.UniversalTypeProgram

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

def typedEntries (P : PackingData V U) (encodeVertex : V → List Bool)
    (encodeType : U → List Bool) : List Entry :=
  P.types.values.map fun u => (encodeType u, (P.bucket u).map encodeVertex)

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

def inverseQueries (D : ℕ) : List (List Bool) :=
  (List.range' 0 D).reverse.map PackingMetadata.unary

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A finite sequence of genuine copy, clear and constant-bit instructions.
The functional result is only a trace specification; execution uses the
fixed primitive instruction tables. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Staging

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

variable {r s : ℕ}

def action (v pr : Fin r) (tmp : Fin s) : Action s → Cmd r s
  | .copy src dst => .call (StackRoutines.copyProgram src dst tmp v pr)
  | .clear dst => .call (StackRoutines.clearProgram dst v pr)
  | .push dst b => TupleProgram.pushConst dst v b

def sequence (v pr : Fin r) (tmp : Fin s) : List (Action s) → Cmd r s
  | [] => .base .skip
  | op::ops => .seq (action v pr tmp op) (sequence v pr tmp ops)

end SubexponentialSAT.SqrtLog.LayoutProgram.Staging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

def MetadataBound (m : GlobalBasisMetadata.Metadata) (S : ℕ) : Prop :=
  m.block.length ≤ S ∧ m.typeCode.length ≤ S ∧ m.rank.length ≤ S

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Materialize incidence labels from actual two-address read plans. The
physical gather reads the head and factor words in that order. Incidence
numbers are the read-plan list positions, including repeated plans. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open SubexponentialSAT.BitProgram

variable {D r Q : ℕ}

theorem labelPlans_valid (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    ∀ plan ∈ labelPlans words address, ∀ j ∈ plan,
      j < (words.map ReadPlan.encodeWord).length := by
  intro plan hplan j hj
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hplan
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · simp
  · simp

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Simultaneous type packing and original-variable head balance. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
noncomputable section

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

def headSupport (ω : WordAssignment V E r Q) (t : Fin Q) (g : Fin r) : Finset V :=
  Finset.univ.filter fun v => ω (.inl v) t = g

omit [Fintype E] [DecidableEq V] [DecidableEq E] [NeZero r] in
@[simp] theorem mem_headSupport (ω : WordAssignment V E r Q) (t : Fin Q)
    (g : Fin r) (v : V) :
    v ∈ headSupport ω t g ↔ ω (.inl v) t = g := by simp [headSupport]

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A deterministic conditional-expectation algorithm with at most four word reads per term. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Algorithm
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def scoreTerm (x y : ℚ) : ScoreTerm I V Q → WordAssignment V E r Q → ℚ
  | .inl (i,j), ω => y^2 *
      (if incidenceType ivar factor ω i = incidenceType ivar factor ω j then 1 else 0)
  | .inr (t,v,w), ω => x^2 * (if ω (.inl v) t = ω (.inl w) t then 1 else 0)

def scoreOffset (x y : ℚ) : ℚ :=
  y^2 * (Fintype.card I : ℚ)^2 / (Fintype.card (UniversalType r Q 1) : ℚ) +
    x^2 * (Q : ℚ) * (Fintype.card V : ℚ)^2 / (r : ℚ)

variable [NeZero r]

def numberedScoreTerm (indices : List (V ⊕ E)) (x y : ℚ) (z : ScoreTerm I V Q) :
    (ℕ → Word r Q) → ℚ :=
  reindexTerm (indexCode indices) (scoreTerm ivar factor x y z)

/-- Actual finite word search. It evaluates only local completions at each choice. -/
def computedWords (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) :
    WordAssignment V E r Q :=
  let values := localAssign a tail terms (numberedScoreSupport ivar factor indices)
    (numberedScoreTerm ivar factor indices x y)
    (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a indices.length
  fun i => decode a values (indexCode indices i)

end Algorithm
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScores
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Denominator-cleared scores for incidence/head conditional expectation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def naturalTerm (w : Weights) : ScoreTerm I V Q → WordAssignment V E r Q → ℕ
  | .inl (i,j), ω => if incidenceType ivar factor ω i = incidenceType ivar factor ω j
      then w.incidence else 0
  | .inr (t,v,u), ω => if ω (.inl v) t = ω (.inl u) t then w.head else 0

def numberedTerm (indices : List (V ⊕ E)) (w : Weights) (z : ScoreTerm I V Q)
    (ω : ℕ → Word r Q) : ℕ :=
  naturalTerm ivar factor w z (fun i => ω (indexCode indices i))

def numerator (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (w : Weights) (remaining : List ℕ)
    (ω : ℕ → Word r Q) : ℕ :=
  commonNumerator alphabet terms (numberedTerm ivar factor indices w)
    (numberedScoreSupport ivar factor indices) 4 remaining ω

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Splitting all weighted completions into two unweighted integer counts. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def sequentialNumerator (alphabet : List (Word r Q)) (terms : List (ScoreTerm I V Q))
    (indices : List (V ⊕ E)) (w : Weights) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : ℕ :=
  numerator ivar factor alphabet terms indices w (List.range' fixed.length n) (decode default fixed)

end Scores
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramController
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed dynamic assignment controller, specialized to the new exact
weighted scores. The producer contract is explicit and must be discharged by
an actual score-stream program; it is not a unit-cost score operation. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp
open SubexponentialSAT.SqrtLog.Packing SubexponentialSAT.MulticolorTypes

section Controller
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def selectedValues (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (w : Weights) :
    List (Word r Q) :=
  NaturalAssignment.assignNat a tail
    (sequentialNumerator ivar factor (a::tail) terms indices w a) indices.length []

end Controller
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

@[simp] theorem operators_zero (mul : Bool) : operators mul 0 = [] := rfl

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TensorSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Tensor eigenbases for the multicolor register swap

The finite change of basis is constructed from invertible local kernels. This
module then specializes it to the actual register swap and transports it to the
joint fiber of universal types; multiplicities count those actual basis labels.
-/

namespace SubexponentialSAT.Subexp.TensorSpectrum

open scoped BigOperators

section JointBasis

open SubexponentialSAT.MulticolorTypes

variable {r Q Δ : ℕ}

/-- Negative signs are indexed by the local labels strictly below the diagonal. -/
def negativePositions {t : Fin Q} {g : Fin r} {i : Fin Δ} (a : JointBasisIndex t g i) :
    Finset (Fin Q) :=
  (Finset.univ.filter fun l : OtherPosition t => (a.2 l).2 < (a.2 l).1).map
    ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem mem_negativePositions {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) (l : OtherPosition t) :
    l.val ∈ negativePositions a ↔ (a.2 l).2 < (a.2 l).1 := by
  simp only [negativePositions, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj, hjl⟩
    have h : j = l := Subtype.ext hjl
    simpa only [h] using hj
  · intro h
    exact ⟨l, h, rfl⟩

def jointWeight {t : Fin Q} {g : Fin r} {i : Fin Δ} (a : JointBasisIndex t g i) : ℕ :=
  SubexponentialSAT.SubexpSwapMultiplicity.swapWeight a.2

@[simp] theorem card_negativePositions {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) : (negativePositions a).card = jointWeight a := by
  simp [negativePositions, jointWeight, SubexponentialSAT.SubexpSwapMultiplicity.swapWeight,
    SubexponentialSAT.SubexpSwapMultiplicity.weight, SubexponentialSAT.SubexpSwapMultiplicity.negativeSupport,
    SubexponentialSAT.SubexpSwapMultiplicity.negativePair]
  rfl

def jointSign (K : Type*) [Field K] {t : Fin Q} {g : Fin r} {i : Fin Δ}
    (a : JointBasisIndex t g i) (l : Fin Q) : K :=
  if l ∈ negativePositions a then -1 else 1

@[simp] theorem jointSign_other (K : Type*) [Field K]
    {t : Fin Q} {g : Fin r} {i : Fin Δ} (a : JointBasisIndex t g i) (l : OtherPosition t) :
    jointSign K a l.val = LocalSpectrum.eigenvalue K (a.2 l) := by
  simp only [jointSign, mem_negativePositions, LocalSpectrum.eigenvalue, ← not_le, ite_not]

end JointBasis

section Multiplicities

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSwapMultiplicity

variable {r Q Δ : ℕ}

@[simp] theorem card_spectator (g : Fin r) (i : Fin Δ) :
    Fintype.card (Spectator (Q := Q) g i) = spectatorCard r Q Δ := by
  simp [Spectator, spectatorCard, ← pow_mul]

end Multiplicities

end SubexponentialSAT.Subexp.TensorSpectrum

end OAI.Algorithms
end


