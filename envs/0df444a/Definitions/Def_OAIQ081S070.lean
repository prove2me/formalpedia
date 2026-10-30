-- Prove2me | Definitions.Def_OAIQ081S070
-- name    : OAIQ081S070
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:53:47.468513+00:00
-- url     : https://prove2.me/theorems/09208f5c-c8f5-4956-8f7e-a9ecb28454e8
-- title:
--   Definitions bundle OAIQ081S070 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 64 declarations of OpenAI's Lean: 31 definitions, 1 instance and 32 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.totalCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.makeUKeyCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftUCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.constantBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryArrayProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.binaryArrayRepresented`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.coefficientRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.digitPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.digitValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.liftRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.differenceTableBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.inverseBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.inverseTableBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.coefficients`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.search`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.tableWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.foldProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.inverseValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.node`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.residueNode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.unitOfResidue`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.cartesianCmd`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.initCmd`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.tupleCallback`, `OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram.wordCallback`, `OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SubexpKernelControl.emitLiteral`, `OAI.Algorithms.SubexponentialSAT.SubexpScopeMembershipProgram.command`, `OAI.Algorithms.SubexponentialSAT.SubexpScopeMembershipProgram.member`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_HeadScatterProgramRun`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalar`, `SubexponentialSAT_SqrtLog_IdempotentProgramBinary`, `SubexponentialSAT_SqrtLog_IdempotentProgramComplete`, `SubexponentialSAT_SqrtLog_IdempotentProgramCore`, `SubexponentialSAT_SqrtLog_IdempotentProgramOutput`, `SubexponentialSAT_SqrtLog_IdempotentProgramTrace`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgram`, `SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup`, `SubexponentialSAT_SqrtLog_IntegerRingLiftProgramModel`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgram`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramCost`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramNative`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables`, `SubexponentialSAT_SqrtLog_IrreducibleSearch`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation`, `SubexponentialSAT_SqrtLog_LeafProgramRecords`, `SubexponentialSAT_SqrtLog_RingModel`, `SubexponentialSAT_SqrtLog_RingModelNodes`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_StructuredCalls`, `SubexponentialSAT_SubexpIncidenceSlotProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_SubexpScanPrimitives`, `SubexponentialSAT_SubexpScopeMembershipProgram`, `SubexponentialSAT_Subexp_BlockCopyProgram`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S045`, `OAIQ081S046`, `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053` and `OAIQ081S056` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S085`, `OAIQ081S086`, `OAIQ081S087`, `OAIQ081S088`, `OAIQ081S089`, `OAIQ081S090`, `OAIQ081S091`, `OAIQ081S093`, `OAIQ081S095`, `OAIQ081S097` and `OAIQ081S098`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.scalar_value_eq_target`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixAnchorReadProgram.readFour_typed`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S046
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S048
import Definitions.Def_OAIQ081S049
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S052
import Definitions.Def_OAIQ081S053
import Definitions.Def_OAIQ081S056

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StructuredCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Structured invocation of existing finite bit programs

A call contains a fixed finite instruction table. Its execution premise is an
actual trace of that table, rather than a semantic or cost oracle. Compilation
relocates all its instructions and replaces each halt by a return jump. Thus
arbitrary cyclic subroutines can occur inside structured loops without manually
assigning global labels.
-/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

theorem compiled_io_trace {r s : ℕ} {c : Cmd r s} {n : ℕ}
    (inputStack outputStack : Fin s) {input output : List Bool}
    (h : Eval c n (StructuredProgram.ioState inputStack input)
      (StructuredProgram.ioState outputStack output)) :
    Trace (compiled c inputStack outputStack) (n + 1)
      (initial (compiled c inputStack outputStack) input)
      (terminal (compiled c inputStack outputStack) output) :=
  compiled_halt_trace h inputStack outputStack

end SubexponentialSAT.StructuredCalls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScanPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete stack operations used by the serialized coefficient scanner. -/

namespace SubexponentialSAT.SubexpScanPrimitives

open BitProgram StructuredCalls

theorem reverse_eval {r s : ℕ} (d : State r s) (src tmp₁ tmp₂ : Fin s) (v p : Fin r)
    (h₁ : src ≠ tmp₁) (h₂ : src ≠ tmp₂) (h₁₂ : tmp₁ ≠ tmp₂) (hvp : v ≠ p)
    (ht₁ : d.stacks tmp₁ = []) (ht₂ : d.stacks tmp₂ = []) :
    Eval (.call (StackRoutines.reverseProgram src tmp₁ tmp₂ v p))
      (9 * (d.stacks src).length + 7) d (afterReverse d src v p) := by
  apply Eval.call
  have ht := StackRoutines.reverseProgram_trace src tmp₁ tmp₂ v p h₁ h₂ h₁₂ hvp
    d.regs d.stacks ht₁ ht₂
  have hh := StackRoutines.halt_after_trace _ ht 9 rfl rfl
  simpa [afterReverse, StackRoutines.reverseResult, StructuredProgram.State.withPC,
    StackRoutines.reverseProgram, Nat.add_assoc] using hh

end SubexponentialSAT.SubexpScanPrimitives

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

theorem escape_eval {r s : ℕ} (p : RecordPrograms.Ports r s) (base : State r s)
    (bits out : List Bool) (v pr f : Bool) :
    Eval (escape p) (5 * bits.length + 3)
      (RecordPrograms.state p base v pr f bits out)
      (RecordPrograms.state p base false false f [] (escaped bits.reverse ++ out)) := by
  have h := eval_call_lifted escapeProgram (RecordPrograms.registerMap p)
    (RecordPrograms.stackMap p) (RecordPrograms.state p base v pr f bits out)
    (RecordPrograms.registerMap_injective p) (RecordPrograms.stackMap_injective p)
    (a := RecordPrograms.parserState v pr bits out)
    (b := RecordPrograms.parserState false false [] (escaped bits.reverse ++ out))
    (escapeProgram_trace bits out v pr)
  simpa only [RecordPrograms.embed_parserState, escape] using h

theorem pushConst_eval {r s : ℕ} (dst : Fin s) (value : Fin r) (b : Bool)
    (a : State r s) : Eval (pushConst dst value b) 2 a (pushedState dst value b a) := by
  have h := Eval.seq (.base (StructuredProgram.Eval.atom (.set value b) a))
    (.base (StructuredProgram.Eval.atom (.push dst value)
      ((StructuredProgram.Atom.set value b).eval a)))
  simpa [pushConst, RecordPrograms.atom, pushedState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using h

theorem clear_eval {r s : ℕ} (src : Fin s) (value present : Fin r) (a : State r s) :
    Eval (.call (StackRoutines.clearProgram src value present))
      (2 * (a.stacks src).length + 3) a
      ⟨readRegs a.regs value present none, StackRoutines.clearStacks src a.stacks⟩ := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src value present a.regs a.stacks) 2 rfl rfl
  simpa [StructuredProgram.State.withPC, StackRoutines.clearResult,
    StackRoutines.clearProgram, Nat.add_assoc] using h

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

abbrev wordCallback : Cmd 10 9 :=
  .seq (pushConst 5 6 false)
    (.seq (escape wordPorts)
      (.seq (.call (StackRoutines.copyProgram 2 6 7 6 7))
        (.seq (escape tuplePorts) (pushConst 5 6 true))))

abbrev tupleCallback : Cmd 10 9 :=
  .seq (.call (StackRoutines.copyProgram 1 3 7 6 7))
    (.seq (RecordPrograms.iterate innerPorts wordCallback)
      (.call (StackRoutines.clearProgram 2 6 7)))

abbrev cartesianCmd : Cmd 10 9 := RecordPrograms.iterate outerPorts tupleCallback

/-- Install the constant singleton empty tuple and empty output list using
eight real bit instructions. No tuple array is supplied by the caller. -/
abbrev initCmd : Cmd 10 9 :=
  .seq (pushConst 0 6 false) (.seq (pushConst 0 6 false)
    (.seq (pushConst 0 6 true) (pushConst 5 6 false)))

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs for the growing packing parameters

Numbers are little-endian Boolean stacks, with leading zeroes allowed. The
programs below manipulate only bits and stacks; natural-number quantities in
their specifications and cost bounds are not machine registers.
-/

namespace SubexponentialSAT.SubexpParameterProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.CounterPrograms

/-! ## Consume a most-significant zero prefix and the leading one -/

/-! ## Concrete input reversal -/

theorem link_io_runs {r s l m n₁ n₂ : ℕ}
    (p : Program r s l) (q : Program r s m) (h : p.outputStack = q.inputStack)
    (input middle output : List Bool)
    (hp : RunsIn p n₁ (initial p input) (terminal p middle))
    (hq : RunsIn q n₂ (initial q middle) (terminal q output)) :
    RunsIn (ProgramLinking.link p q) (n₁ + n₂)
      (initial (ProgramLinking.link p q) input)
      (terminal (ProgramLinking.link p q) output) := by
  exact ProgramLinking.link_complete_runsIn p q input output hp rfl
    (by simpa only [enter_terminal_eq_initial p q h middle] using hq)

theorem prepareLog_runs (xs : List Bool) :
    RunsIn prepareLogProgram (6 * xs.length + 9)
      (initial prepareLogProgram xs)
      (terminal prepareLogProgram (trimTail xs.reverse)) := by
  have h := link_io_runs reverseTransfer trimProgram rfl xs xs.reverse
    (trimTail xs.reverse) ⟨_, le_rfl, reverseTransfer_trace xs⟩
    (trim_complete_runs xs.reverse)
  convert h using 1
  · simp only [List.length_reverse]
    omega

/-! ## Reindex and call the checked binary word-length counter -/

theorem swappedLength_correct (xs : List Bool) :
    ∃ output, value output = xs.length ∧ output.length ≤ xs.length ∧
      RunsIn swappedLengthProgram (xs.length * (8 * xs.length + 10) + 3)
        (initial swappedLengthProgram xs) (terminal swappedLengthProgram output) := by
  obtain ⟨output, hvalue, hlen, hrun⟩ := length_correct xs
  have h := ProgramLinking.liftProgram_runsIn lengthProgram id swapStacks
    (initial swappedLengthProgram []) Function.injective_id swapStacks.injective hrun
  refine ⟨output, hvalue, hlen, ?_⟩
  simpa only [swappedLengthProgram, lift_equiv_initial, lift_equiv_terminal] using h

/-- Actual fixed-table logarithm program, correct for arbitrary padded words. -/
theorem log_correct (xs : List Bool) :
    ∃ output, value output = Nat.log2 (value xs) ∧ output.length ≤ xs.length ∧
      RunsIn logProgram (logBound xs.length)
        (initial logProgram xs) (terminal logProgram output) := by
  obtain ⟨output, hvalue, hlen, hcount⟩ := swappedLength_correct (trimTail xs.reverse)
  have hrun := link_io_runs prepareLogProgram swappedLengthProgram rfl
    xs (trimTail xs.reverse) output (prepareLog_runs xs) hcount
  have htail : (trimTail xs.reverse).length ≤ xs.length := by
    simpa using trimTail_length_le xs.reverse
  refine ⟨output, hvalue.trans (trimTail_reverse_length xs), hlen.trans htail, hrun.mono ?_⟩
  have hmul := Nat.mul_le_mul htail
    (show 8 * (trimTail xs.reverse).length + 10 ≤ 8 * xs.length + 10 by omega)
  dsimp [logBound]
  nlinarith

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

def totalCost (n : ℕ) (js : List ℕ) (bits : List Bool) : ℕ :=
  initCost js bits n+scanCost js+12

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramRecords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured physical folds over sparse-hash records

This module specializes the audited framed-record iterator to an accumulator
fold which visits every record. The callback is an actual finite `Cmd`; its
local execution contract remains explicit. `foldProgram_run` concerns primitive
Boolean-register/stack transitions, not an operation counter or semantic oracle.
The same program shape handles clause-literal products, sparse weighted sums,
coefficient-array maps, and support-key dictionary scans.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {A : Type*}

abbrev foldProgram (ports : Ports r s) (step : Cmd r s) :
    Program r s (size (foldCommand ports step) + 1) :=
  compiled (foldCommand ports step) ports.source ports.source

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockCopyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for copying a local table into every block

Stack 0 contains the encoded local table, stack 1 the output suffix, stack 2
is empty scratch, and stack 3 contains the unary number of blocks.  The same
finite program handles all table lengths and block counts.  It preserves the
local table and prefixes one copy per block to the output.  This is the compact
block-major representation of the repeated local basis/complement arrays;
scattering their coordinates through the packing is a separate operation.
-/

namespace SubexponentialSAT.Subexp.BlockCopyProgram

open BitProgram StructuredCalls StackRoutines

/-- The compiled finite Boolean-stack machine has the claimed exact trace. -/
theorem program_trace (n : ℕ) (table output : List Bool) :
    Trace program (n * (7 * table.length + 7) + 3)
      ((initialState n table output).withPC (some program.entry))
      ((data false false table (copies n table ++ output) []).withPC none) := by
  simpa only [program, Nat.add_assoc] using
    compiled_halt_trace (command_eval n table output) 0 1

end SubexponentialSAT.Subexp.BlockCopyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierKey. -/

/-! Construction and application of the U monomial by actual native instructions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native


abbrev makeUKeyCommand : Cmd 8 96 := List.foldr Cmd.seq (.base .skip)
  [copy 88 89 70,
   liftCommand HashCircuitProgram.Constant.pad 0 2 id keyPorts,
   liftCommand HashCircuitProgram.Constant.tag 2 2 id keyPorts,
   .base (.atom (.set 0 true)), .base (.atom (.push 91 0)),
   copy 91 94 70, clear 91]

abbrev shiftUCommand : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram Squarefree.KeyMapProgram.scanProgram id mapPorts)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable Newton control over a supplied represented coefficient ring.
The measured counters below charge every callback and seven control events.
They are an intermediate interface, not a primitive bit-runtime certificate;
the supplied callbacks must be refined by actual serialized-array services. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*} [CommRing R]

/-- Runtime iteration count is logarithmic; no unary `t` Newton loop. -/
def liftRun (ops : RingProgram C) (e : C) (t : ℕ) : C × ℕ :=
  iterateRun ops e (Nat.clog 2 t)

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramOutput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

/-- Complete finite array construction, with a measured initial stage. -/
def coefficientRun (ops : RingProgram C) (t : ℕ) (u : C) : (Fin (3*t) → C) × ℕ :=
  let setup := tableConstructionRun ops t
  let initial := initialRun ops t u
  let program := RingProgram.program ops setup.1 (zeroCode ops t) (oneCode ops t)
  let out := liftRun program initial.1 t
  (out.1, setup.2 + initial.2 + out.2 + 1)

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

def digitValue (ops : RepresentedRing C A) (φ : A →+* R) {t : ℕ}
    (v : Fin (3*t) → C) (s : Fin t) (x : R) : R :=
  ∑ a : Fin 3, φ (ops.decode (digitCode v s a)) * x^a.val

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R K : Type*} [CommRing A] [CommRing R] [CommRing K]

/-- A semantic view of three stored coefficients, not an implementation step. -/
noncomputable def digitPolynomial (ops : RepresentedRing C A) {t : ℕ}
    (v : Fin (3*t) → C) (s : Fin t) : Polynomial A :=
  ∑ a : Fin 3, Polynomial.monomial a.val (ops.decode (digitCode v s a))

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramTrace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed four-register Newton instruction stream and its exact execution
relation. Registers contain coefficient arrays at the intended instantiation.
This is an arithmetic-register trace, not yet a native Boolean-stack trace. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*} [CommRing R]

theorem newtonCode_result (ops : RingProgram C) (state : Registers C) :
    (codeRun ops newtonCode state).1 0 = (newtonRun ops (state 0)).1 := by
  simp [codeRun, newtonCode, instructionRun, newtonRun, Function.update]

end SubexponentialSAT.SqrtLog.IdempotentProgram

namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

/-- Exact code-word correspondence, independent of any semantic decoder. -/
theorem liftCode_result {C : Type*} (ops : RingProgram C) (n : ℕ) (state : Registers C) :
    (codeRun ops (liftCode n) state).1 0 = (iterateRun ops (state 0) n).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [liftCode, codeRun_append]
      change (codeRun ops newtonCode (codeRun ops (liftCode n) state).1).1 0 = _
      rw [newtonCode_result, ih]
      rfl

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramBinary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Negation through multiplication by a cached negative unit. This permits
the native implementation to use only addition and multiplication services. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

@[simp] theorem binaryRepresented_decode (ops : RepresentedRing C R) (minusOne : C)
    (hm : ops.decode minusOne = -1) :
    (binaryRepresented ops minusOne hm).decode = ops.decode := rfl

theorem minusOneRun_correct (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) :
    evaluate ops φ t x (minusOneRun ops.program t).1 = -1 := by
  change RingProgram.denote ops φ (hadicBasis t x)
    (RingProgram.negRun ops.program (oneCode ops.program t)).1 = _
  rw [RingProgram.denote_neg]
  exact congrArg Neg.neg (evaluate_one ops φ t x ht)

def binaryArrayProgram (ops : RingProgram C) (t : ℕ) : RingProgram (Fin (3*t) → C) :=
  binaryProgram (arrayProgram ops t) (minusOneRun ops t).1

abbrev binaryArrayRepresented (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) : RepresentedRing (Fin (3*t) → C) R :=
  binaryRepresented (arrayRepresented ops φ t x ht) (minusOneRun ops.program t).1
    (minusOneRun_correct ops φ t x ht)

@[simp] theorem binaryArrayRepresented_program (ops : RepresentedRing C A) (φ : A →+* R)
    (t : ℕ) (x : R) (ht : hValue x ^ t = 0) :
    (binaryArrayRepresented ops φ t x ht).program = binaryArrayProgram ops.program t := rfl

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native refinements for the scalar coefficient reader and injector.
All stacks outside the named outputs are preserved, including the ambient
low-product environment. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar
open BitProgram StructuredCalls
open HashCircuitProgram.Native

def constantBytes (shapeLength : ℕ) (coeff : List Bool) : List Bool :=
  Encoding.frame (HashCircuitProgram.Constant.key shapeLength) ++ Encoding.frame coeff

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

theorem emit_eval (d : Data) (c : Fin 6) :
    Eval (emit c) 3 d ⟨setOutput d.regs c,d.stacks⟩ := by
  convert Eval.base (SubexpParameterProgram.atoms_eval
    [.set 5 (codeBits c 0), .set 6 (codeBits c 1), .set 7 (codeBits c 2)] d) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · funext i; fin_cases i <;> simp [setOutput,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,StructuredProgram.State.ofCfg,execInstr]
  · rfl

theorem lookup_eval (cs : List (Fin 6)) (n : ℕ) (r : Fin 8 → Bool)
    (xs ys bs : List Bool) :
    ∃ steps rf zs, steps ≤ 2*cs.length+3 ∧
      Eval (lookup cs) steps (data r xs ys (List.replicate n true) bs)
        (data rf xs ys zs bs) ∧
      (∀ b : Fin 3, rf (outputPort b) = codeBits (cs[n]?.getD 0) b) ∧ zs.length ≤ n := by
  induction cs generalizing n r with
  | nil =>
      refine ⟨3,setOutput r 0,List.replicate n true,by simp,emit_eval _ 0,?_,by simp⟩
      intro b; fin_cases b <;> simp [setOutput,outputPort]
  | cons c cs ih =>
      cases n with
      | zero =>
          let rr := readRegs r (0 : Fin 8) 1 none
          have he := (popLookup r xs ys [] bs).seq
            (Eval.ite_false (test := 1) (yes := lookup cs) (by simp [data,readRegs])
              (emit_eval (data rr xs ys [] bs) c))
          refine ⟨5,setOutput rr c,[],by simp only [List.length_cons] ; omega,he,?_,by simp⟩
          intro b
          fin_cases b <;> simp [setOutput, outputPort]
      | succ n =>
          let rr := readRegs r (0 : Fin 8) 1 (some true)
          obtain ⟨steps,rf,zs,hcost,he,hbits,hz⟩ := ih n rr
          refine ⟨steps+2,rf,zs,by simp only [List.length_cons] ; omega,?_,?_,by omega⟩
          · simpa [lookup,List.replicate_succ,Nat.add_comm,Nat.add_left_comm,
              Nat.add_assoc] using
              (popLookup r xs ys (true :: List.replicate n true) bs).seq
                (Eval.ite_true (test := 1) (no := emit c) (by simp [data,readRegs]) he)
          · simpa using hbits

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar preparation contract for the 41-stack H-adic setup.
All generated constants are canonical; the selector and array builder receive
exact functional words. The only unbounded iteration uses cached unary t. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing BinaryArithmetic

theorem budget_polynomial (t W:ℕ) :
    400*(baseWidth 3 t+W+1)+(3*t+10)*stepBudget 3 t+9*t+4*baseWidth 3 t+13
      ≤ 500000*(t+W+1)^3 := by
  simp only [stepBudget,RingProgram.ternary_baseWidth]
  nlinarith [Nat.zero_le (t^3),Nat.zero_le (t*W),Nat.zero_le (t^2*W),Nat.zero_le (t*W^2),Nat.zero_le (W^3)]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual fixed bit programs for the two logarithmic setup quantities.
Input and output numbers are arbitrary padded little-endian words. -/
namespace SubexponentialSAT.SqrtLog.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

theorem logarithm_eval (xs : List Bool) :
    ∃ output t, value output = Nat.log2 (value xs) ∧ output.length ≤ xs.length ∧
      t ≤ SubexpParameterProgram.logBound xs.length ∧
      Eval logarithm t (io xs) (io output) := by
  obtain ⟨output, hv, hl, t, ht, he⟩ := SubexpParameterProgram.log_correct xs
  exact ⟨output, t, hv, hl, ht, .call _ he⟩

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentTableEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native table-entry selector. The only input magnitudes are unary
stack data. Output registers 5,6,7 encode the six possible small coefficients. -/
namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

theorem selectJ_eval (a : ℕ) (b : Fin 3) (n : ℕ)
    (r : Fin 8 → Bool) (xs ys bs : List Bool)
    (h5 : r 5 = decide (b.val=1)) (h6 : r 6 = decide (b.val=2)) :
    ∃ steps rf zs, steps ≤ 15 ∧
      Eval (selectJ a) steps (data r xs ys (List.replicate n true) bs)
        (data rf xs ys zs bs) ∧
      (∀ z, rf (outputPort z) =
        codeBits (((coefficientsAt (a+b.val))[n]?).getD 0) z) ∧ zs.length ≤ n := by
  obtain ⟨steps,rf,zs,hc,he,hbits,hz⟩ := lookup_eval (coefficientsAt (a+b.val)) n r xs ys bs
  rw [coefficientsAt_length] at hc
  refine ⟨steps+(if b.val=1 then 1 else 2),rf,zs,by split_ifs <;> omega,?_,hbits,hz⟩
  fin_cases b
  · simpa [selectJ,Nat.add_assoc] using Eval.ite_false (test := 5) (yes := lookup (coefficientsAt (a+1))) h5
      (Eval.ite_false (test := 6) (yes := lookup (coefficientsAt (a+2))) h6 he)
  · simpa [selectJ,Nat.add_assoc] using Eval.ite_true (test := 5)
      (no := .ite 6 (lookup (coefficientsAt (a+2))) (lookup (coefficientsAt a))) h5 he
  · simpa [selectJ,Nat.add_assoc] using Eval.ite_false (test := 5) (yes := lookup (coefficientsAt (a+1))) h5
      (Eval.ite_true (test := 6) (no := lookup (coefficientsAt a)) h6 he)

theorem select_eval (a b : Fin 3) (n : ℕ)
    (r : Fin 8 → Bool) (xs ys bs : List Bool)
    (h3 : r 3 = decide (a.val=1)) (h4 : r 4 = decide (a.val=2))
    (h5 : r 5 = decide (b.val=1)) (h6 : r 6 = decide (b.val=2)) :
    ∃ steps rf zs, steps ≤ 17 ∧
      Eval select steps (data r xs ys (List.replicate n true) bs)
        (data rf xs ys zs bs) ∧
      (∀ z, rf (outputPort z) =
        codeBits (((coefficientsAt (a.val+b.val))[n]?).getD 0) z) ∧ zs.length ≤ n := by
  obtain ⟨steps,rf,zs,hc,he,hbits,hz⟩ := selectJ_eval a.val b n r xs ys bs h5 h6
  refine ⟨steps+(if a.val=1 then 1 else 2),rf,zs,by split_ifs <;> omega,?_,hbits,hz⟩
  fin_cases a
  · simpa [select,Nat.add_assoc] using Eval.ite_false (test := 3) (yes := selectJ 1) h3
      (Eval.ite_false (test := 4) (yes := selectJ 2) h4 he)
  · simpa [select,Nat.add_assoc] using Eval.ite_true (test := 3) (no := .ite 4 (selectJ 2) (selectJ 0)) h3 he
  · simpa [select,Nat.add_assoc] using Eval.ite_false (test := 3) (yes := selectJ 1) h3
      (Eval.ite_true (test := 4) (no := selectJ 0) h4 he)

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite bit program constructs the ternary H-adic lift from its
binary precision alone. Preparation, array arithmetic, iteration and output
serialization are all covered by actual bit-instruction traces. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing

theorem nativeLiftBudget_mono (t : ℕ) {a b : ℕ} (h : a ≤ b) :
    nativeLiftBudget t a ≤ nativeLiftBudget t b := by
  unfold nativeLiftBudget
  gcongr

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

instance fieldE : Field a.E := LiftRing.extensionField a.residuePolynomial_irreducible

theorem rho_eq_zero_iff (ht : 0 < t) (x : a.O t) :
    a.rho t ht x = 0 ↔ (3 : a.O t) ∣ x := by
  change a.reducedEquiv t ht (LiftRing.residue 3 t ht (a.F t) x) = 0 ↔ _
  rw [← (a.reducedEquiv t ht).map_zero, (a.reducedEquiv t ht).injective.eq_iff]
  exact LiftRing.residue_eq_zero_iff 3 t ht (a.F_monic t ht) x

theorem prime_power_zero : (3 : a.O t) ^ t = 0 := LiftRing.prime_power_zero 3 t (a.F t)

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IntegerRingLiftProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete, fixed native programs lifting a pair of arbitrary little-endian
binary words to the actual RingModel. There is no integer-lifting callback.
The only runtime constants are explicit represented ring caches. -/
namespace SubexponentialSAT.SqrtLog.IntegerRingLiftProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open CRTLocalProgram (lowFrame_refl)

/-- Explicit polynomial bound in input bit length, extension degree and scalar
word width. No dependence on the integers' magnitudes occurs. -/
theorem modelScaledBudget_polynomial (bits t d : ℕ) :
    modelScaledBudget bits t d ≤
      bits * (100000*(d+1)^3*(baseWidth 3 t+1)^2 + 80*d*baseWidth 3 t + 110) +
        200000*(d+1)^3*(baseWidth 3 t+1)^2 + 203*d*baseWidth 3 t + 251 := by
  have hm := HornerProgram.Services.mulBudget_polynomial (baseWidth 3 t) d
  have ha := HornerProgram.Services.addBudget_polynomial (baseWidth 3 t) d
  have hs := Nat.mul_le_mul_left bits (Nat.mul_le_mul_left 2 ha)
  unfold modelScaledBudget scaledBudget signedBudget
  ring_nf at *
  omega

end SubexponentialSAT.SqrtLog.IntegerRingLiftProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModelNodes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit radix-indexed nodes for the supplied-polynomial ring model. -/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel.Data

variable {d : ℕ} (a : RingModel.Data d) (t Q : ℕ)

/-- Index a residue by its base-three coefficient digits. -/
def fieldIndex : a.E ≃ Fin (3 ^ d) :=
  a.fieldCoordinates.toEquiv.trans
    ((Equiv.piCongrRight fun _ : Fin d => (ZMod.finEquiv 3).symm.toEquiv).trans
      finFunctionFinEquiv)

@[simp] theorem fieldIndex_zero : a.fieldIndex 0 = 0 := by
  apply Fin.ext
  simp [fieldIndex ]

/-- Node i is the residue whose coefficient word has radix index i+1. -/
def residueNode (hQ : Q < 3 ^ d) (i : Fin Q) : a.E :=
  a.fieldIndex.symm ⟨i.val + 1, by omega⟩

def node (ht : 0 < t) (hQ : Q < 3 ^ d) (i : Fin Q) : a.O t :=
  a.sectionValue t ht (a.residueNode Q hQ i)

@[simp] theorem rho_node (ht : 0 < t) (hQ : Q < 3 ^ d) (i : Fin Q) :
    a.rho t ht (a.node t Q ht hQ i) = a.residueNode Q hQ i := a.rho_sectionValue t ht _

def inverseValue (ht : 0 < t) (x : a.O t) : a.O t :=
  NilpotentDefect.residueInverse (a.rho t ht) (a.sectionValue t ht) t x

theorem mul_inverseValue (ht : 0 < t) (x : a.O t) (hx : a.rho t ht x ≠ 0) :
    x * a.inverseValue t ht x = 1 :=
  NilpotentDefect.mul_residueInverse (a.rho t ht) (a.sectionValue t ht)
    (a.rho_sectionValue t ht) (3 : a.O t) t (a.prime_power_zero t)
    (fun z hz => (a.rho_eq_zero_iff t ht z).mp hz) x hx

def unitOfResidue (ht : 0 < t) (x : a.O t) (hx : a.rho t ht x ≠ 0) : (a.O t)ˣ where
  val := x
  inv := a.inverseValue t ht x
  val_inv := a.mul_inverseValue t ht x hx
  inv_val := by rw [mul_comm]; exact a.mul_inverseValue t ht x hx

@[simp] theorem unitOfResidue_val (ht : 0 < t) (x : a.O t) (hx : a.rho t ht x ≠ 0) :
    (a.unitOfResidue t ht x hx : a.O t) = x := rfl

end SubexponentialSAT.SqrtLog.RingModel.Data

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite arithmetic subprograms used in the cache scans. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing

def inverseBudget (t d : ℕ) := CRTLocalProgram.NativeInverse.budget t d + 1

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete ordered native tables; all working streams are empty again. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

def inverseTableBudget (t d Q : ℕ) :=
  nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) Q+9*(d*baseWidth 3 t)+9*(Q*(d*baseWidth 3 t))+15

def differenceTableBudget (t d Q : ℕ) :=
  Q*(nodeScanBudget (inverseBudget t d) (d*baseWidth 3 t) Q+23*(d*baseWidth 3 t)+16)+9*(Q*(Q*(d*baseWidth 3 t)))+14

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single fixed native interpolation-cache producer. The only data
inputs are the actual node stream and already prepared ring constants.
No inverse, negative, or pairwise table is supplied to this program. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing

def budget (t d Q : ℕ) := inverseTableBudget t d Q + negativeTableBudget t d Q +
  differenceTableBudget t d Q + 11*(Q*(d*baseWidth 3 t))+9+11*(d*baseWidth 3 t)+9

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical table producer has polynomial cost in the node count,
residue cardinality, precision, and the native ring-operation bounds. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT SubexpLiftRing

theorem budget_le_operations (t d Q : ℕ) :
    budget t d Q+1 ≤ (Q+1)^2 *
      (inverseBudget t d+negativeBudget t d+200*(d*baseWidth 3 t)+200) := by
  unfold budget inverseTableBudget negativeTableBudget differenceTableBudget nodeScanBudget
  ring_nf
  omega

theorem inverseBudget_polynomial (t d : ℕ) :
    inverseBudget t d ≤ 600*(3^d+t+1)*
      (HornerProgram.Services.mulBudget (baseWidth 3 t) d+
        HornerProgram.Services.addBudget (baseWidth 3 t) d+d*baseWidth 3 t+1) := by
  let Km := HornerProgram.Services.mulBudget (baseWidth 3 t) d
  let Ka := HornerProgram.Services.addBudget (baseWidth 3 t) d
  let W := d*baseWidth 3 t
  change (3^d-2+t+1)*(4*Km+4*Ka+300*W+400)+Km+Ka+102*W+113+1 ≤ _
  have hsub : 3^d-2+t+1 ≤ 3^d+t+1 :=
    Nat.add_le_add_right (Nat.add_le_add_right (Nat.sub_le (3^d) 2) t) 1
  have hp := Nat.mul_le_mul_right (4*Km+4*Ka+300*W+400) hsub
  change _ ≤ 600*(3^d+t+1)*(Km+Ka+W+1)
  nlinarith only [hp,Nat.zero_le (3^d*Km),Nat.zero_le (3^d*Ka),Nat.zero_le (3^d*W),
    Nat.zero_le (t*Km),Nat.zero_le (t*Ka),Nat.zero_le (t*W),Nat.zero_le Km,Nat.zero_le Ka,Nat.zero_le W,Nat.zero_le (3^d),Nat.zero_le t]

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable arbitrary-degree irreducible search over F₃

Search all monic degree-`d` coefficient vectors and reject each candidate
which is the product of two nonconstant arrays of degree at most `d`.
The test uses explicit convolution. Mathematical finite-field existence
proves that the executable search succeeds for every positive `d`.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

theorem mem_factorPairs (d : ℕ) (a b : Fin (d + 1) → F) : (a, b) ∈ factorPairs d := by
  apply List.mem_flatMap.mpr
  exact ⟨a, mem_candidates _ _, List.mem_map.mpr ⟨b, mem_candidates _ _, rfl⟩⟩

/-- Result, number of candidate tests, number of factor-pair tests. -/
def search (d : ℕ) : Option (Fin d → F) × ℕ × ℕ :=
  QuarticSearch.scan evaluate (candidates d)

/-- Total coefficient selection; positivity proves that the default is unused. -/
def coefficients (d : ℕ) : Fin d → F := (search d).1.getD (fun _ => 0)

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed framed call generates an ordered table from a runtime unary depth.
Only its output and depth ports change; the generator's sentinel is paid for
and cleared before returning. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open Subexp.TupleProgram SubexpOrderedTupleData
open SubexpEnumerationPayload SubexpTupleRefinement

def tableWord (d : ℕ) : List Bool := ProgramEncoding.encodeRecords
  ((IrreducibleSearch.candidates d).map (encodeTuple (scalarCode 3)))

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


/-! Paid construction of both search tables from a single unary depth word. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeMembershipProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete scope-membership subroutine for incidence-plan preparation.
The reversed scope record occupies stack 8 and the reversed query stack 2.
Stacks 0,1,3,4 are empty work ports; all remaining stacks are framed.
-/
namespace SubexponentialSAT.SubexpScopeMembershipProgram

open BitProgram StructuredCalls

abbrev member : Cmd 10 10 :=
  .call (ProgramLinking.liftProgram
    (StructuredCalls.compiled ExecCNFSubset.memberCall 3 4) id stackMap)

abbrev command : Cmd 10 10 := .seq transfer (.seq member (.seq (clear 0) (clear 1)))

end SubexponentialSAT.SubexpScopeMembershipProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls

def finish : Code := .seq (push 3 true) (WorkspaceCleanupProgram.command 0 1 cleanupPorts)

end SubexponentialSAT.SubexpIncidenceSlotProgram

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

/-! ## Fixed source-constructor control -/

abbrev emitLiteral (source : Fin 8) : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram SubexpHornerProgram.Literal.program id
    (tripleMap source 3 4))

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end


