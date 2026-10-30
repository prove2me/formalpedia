-- Prove2me | Definitions.Def_OAIQ081S098
-- name    : OAIQ081S098
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:18:39.130104+00:00
-- url     : https://prove2.me/theorems/0a0a89e4-1caf-43f1-b36f-3dcf0cfe922b
-- title:
--   Definitions bundle OAIQ081S098 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 25 definitions and 29 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.ScaleData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgram.scaleInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.castJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaFrames.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaFrames.afterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaFrames.afterTransfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries.EmitData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries.emitOneStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.afterFrame8`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.afterNat`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.afterTransfer8`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.prependData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.readRecordResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.MatrixState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.ScanState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor.runAtoms`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup.increment`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup.logarithm`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.CanonicalHigh.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.Data`, `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.contextStore`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLogSpace_CodeChecks`, `SubexponentialSAT_SqrtLogSpace_CommandStackTransport`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_SparseCodeProgram`, `SubexponentialSAT_SqrtLogSpace_TruncatedRing`, `SubexponentialSAT_SqrtLog_PackingProgramScale`, `SubexponentialSAT_SqrtLog_PackingWeightProgram`, `SubexponentialSAT_SqrtLog_PackingWeightProgramBasic`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyRelStored`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgram`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramFrames`, `SubexponentialSAT_SqrtLog_ProgramTapeReplay`, `SubexponentialSAT_SqrtLog_RowSelectionProgramEntriesEmit`, `SubexponentialSAT_SqrtLog_SquarefreeProgramNat`, `SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend`, `SubexponentialSAT_SqrtLog_SquarefreeProgramRead`, `SubexponentialSAT_SubexpInputZip`, `SubexponentialSAT_SubexpRowPostfixFrames`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_AssignmentInitProgram`, `SubexponentialSAT_Subexp_AssignmentInputCall`, `SubexponentialSAT_Subexp_AssignmentRecordViews`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S064`, `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S075`, `OAIQ081S076`, `OAIQ081S078`, `OAIQ081S079` and `OAIQ081S080` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S114` and `OAIQ081S115`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.local_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.flat_run`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S064
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S075
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S078
import Definitions.Def_OAIQ081S079
import Definitions.Def_OAIQ081S080

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

abbrev Data := State 16 24

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
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

theorem beforeCopies_temporary {S : ℕ} (tmp : Fin S) (ports : List (Fin S)) (a : Data S) :
    (beforeCopies tmp ports a).stacks tmp = [] := by
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks]
  simp

theorem prepare_temporary {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S)
    (hp : ∀ p ∈ inputs, p.1 ≠ p.2 ∧ p.1 ≠ tmp ∧ tmp ≠ p.2) :
    (prepareState tmp ports inputs a).stacks tmp = [] := by
  exact (copyMany_frame inputs (beforeCopies tmp ports a) tmp
    (fun p hm => (hp p hm).2.2)).trans (beforeCopies_temporary tmp ports a)

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CodeChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Space of the concrete sparse-code predicates

The local-code and Walsh predicates are polynomial-time bit programs. These bounds apply
to every candidate, including losing candidates, and every stack in each actual source
prefix. They are intended as the body estimates of bounded-memory enumeration; the
materialized candidate-family programs are not used here.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- Both scans use fixed finite control and retain one encoded counter tuple. -/
abbrev ScanState := State 16 40

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay under replacement of syntactically untouched tapes. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls

variable {r s l : ℕ}

/-- Same finite execution length, same registers, and the same visible output tapes. -/
theorem eval_rebase (H : Fin s → Prop) [DecidablePred H]
    {c : StructuredCalls.Cmd r s} (hc : AvoidsCmd H c)
    {n : ℕ} {a b : StructuredProgram.State r s} (h : StructuredCalls.Eval c n a b)
    (frame : Fin s → List Bool) :
    StructuredCalls.Eval c n (rebaseState H frame a) (rebaseState H frame b) := by
  induction h with
  | base he => exact .base (base_eval_rebase H hc he frame)
  | call p ht => exact .call p (trace_rebase H hc ht frame)
  | seq h₁ h₂ ih₁ ih₂ => exact .seq (ih₁ hc.1) (ih₂ hc.2)
  | ite_true ht he ih => exact .ite_true ht (ih hc.1)
  | ite_false ht he ih => exact .ite_false ht (ih hc.2)
  | while_false ht => exact .while_false ht
  | while_true ht hb hw ihb ihw => exact .while_true ht (ihb hc) (ihw hc)

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandStackTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! All-prefix resource transport for the existing exact-time tape replay.
The imported avoidance certificate excludes reads as well as writes, including
`peek`. Erasing hidden caller data is a proof construction only: the actual
instruction table and its measured number of steps remain unchanged. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

variable {r s l : ℕ}

theorem rebaseState_restore (H : Fin s → Prop) [DecidablePred H]
    (frame : Fin s → List Bool) (a : State r s) :
    rebaseState H a.stacks (rebaseState H frame a) = a := by
  cases a with
  | mk regs words =>
      apply congrArg (fun ws => (⟨regs, ws⟩ : State r s))
      funext i
      by_cases hi : H i <;> simp [rebaseState, rebaseStacks, hi]

/-- A concrete parameter bank disjoint from hidden storage is unchanged by
the proof-only shadow projection. Registers are always retained. -/
theorem projectState_rebase {R S : ℕ} (H : Fin S → Prop) [DecidablePred H]
    (frame : Fin S → List Bool) (a : State R S)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hstack : ∀ i, ¬ H (stack i)) :
    projectState register stack (rebaseState H frame a) = projectState register stack a := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    exact rebaseStacks_of_not_mem H frame a.stacks (stack i) (hstack i)

/-- Only hidden caller stacks contribute the frame bound. Every visible stack
is controlled by the actual local trace, with no multiplicative recurrence. -/
theorem trace_stack_bound (H : Fin s → Prop) [DecidablePred H]
    {p : Program r s l} (hp : AvoidsProgram H p)
    (frame : Fin s → List Bool) {steps bound frameBound : ℕ} {a b : Cfg r s l}
    (ht : Trace p steps a b)
    (hsource : ∀ prefixSteps source, prefixSteps ≤ steps →
      Trace p prefixSteps a source →
      ∀ i, ¬ H i → (source.stacks i).length ≤ bound)
    (hframe : ∀ i, H i → (frame i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace p prefixSteps (rebaseCfg H frame a) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  intro prefixSteps intermediate hle hprefix i
  obtain ⟨source, hs, rfl⟩ := trace_prefix_rebase H hp frame ht hle hprefix
  by_cases hi : H i
  · change (rebaseStacks H frame source.stacks i).length ≤ _
    rw [rebaseStacks_of_mem H frame source.stacks i hi]
    exact (hframe i hi).trans (Nat.le_max_right _ _)
  · change (rebaseStacks H frame source.stacks i).length ≤ _
    rw [rebaseStacks_of_not_mem H frame source.stacks i hi]
    exact (hsource prefixSteps source hle hs i hi).trans (Nat.le_max_left _ _)

/-- A local execution on the empty hidden shadow yields an execution of the
same fixed command on the actual caller, at exactly the same step count. -/
theorem eval_shadow (H : Fin s → Prop) [DecidablePred H]
    {command : Cmd r s} (hc : AvoidsCmd H command)
    {steps : ℕ} {a b : State r s}
    (he : Eval command steps (rebaseState H (fun _ => []) a) b) :
    Eval command steps a (rebaseState H a.stacks b) := by
  have h := eval_rebase H hc he a.stacks
  rw [rebaseState_restore] at h
  exact h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual floor and ceiling logarithm bit programs, without packing or schedule imports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

open OAI.Algorithms.SubexponentialSAT.BitProgram
open OAI.Algorithms.SubexponentialSAT.CounterPrograms

def runAtoms {r s : ℕ} : List (StructuredProgram.Atom r s) →
    StructuredProgram.State r s → StructuredProgram.State r s
  | [], d => d
  | op :: ops, d => runAtoms ops (op.eval d)

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Floor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 3 3

def increment : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) id incrementPorts)

def logarithm : Cmd 3 3 := .call Floor.logProgram


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 3 3


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

theorem first_trace (v p f : Bool) (bits : List Bool) (rows : List (List Bool)) :
    Trace firstProgram (9 * bits.length + 10)
      ((data v p f (ProgramEncoding.encodeRecords (bits :: rows)) [] []).withPC
        (some firstProgram.entry))
      ((data false false false (ProgramEncoding.encodeRecords rows) [] bits).withPC none) := by
  have h1 := pop_eval v p f true
    (Encoding.frame bits ++ ProgramEncoding.encodeRecords rows) [] []
  have h2 := parse_eval v true true bits (ProgramEncoding.encodeRecords rows) [] []
  simp only [List.append_nil] at h2
  have h3 := transfer_eval false true true (ProgramEncoding.encodeRecords rows) bits.reverse []
  simp only [List.reverse_reverse, List.append_nil] at h3
  have h4 := setFlag_eval false false true (ProgramEncoding.encodeRecords rows) [] bits
  have h := h1.seq (h2.seq (h3.seq h4))
  have hr := compiled_halt_trace h 0 2
  convert hr using 1
  · rfl
  · simp only [List.length_reverse]
    omega
  · simp [firstProgram, ProgramEncoding.encodeRecords, Encoding.encodeList]

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace CanonicalHigh
open DisjointReuse

abbrev Data := State 40 896

open OAI.Algorithms.SubexponentialSAT.StackRoutines

end CanonicalHigh


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- The outer search retains only its current tuple, first witness, and a
constant number of linear-size conversion buffers above the checker's ports. -/
abbrev MatrixState := State 16 48

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Dense lifting and Taylor coefficients

`Truncated R n` stores exactly `n` coefficients. Its multiplication is the
existing total-order convolution, and its ring laws follow from the surjective
coefficient projection from `R[X]`. Nesting the construction stores the shared
lifting marker outside the Taylor variable. The final marker readout is additive.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrder

namespace Truncated

variable {R : Type*} {n : ℕ}

section Semiring

variable [CommSemiring R]

noncomputable section

@[simp] theorem ofPolynomial_nsmul (k : ℕ) (P : Polynomial R) :
    ofPolynomial n (k • P) = k • ofPolynomial n P := by
  ext j
  change (k • P).coeff j.val = k • P.coeff j.val
  exact Polynomial.coeff_smul k P j.val

end
end Semiring

end Truncated

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramScale
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary-counted copier scales a unary score, preserving both inputs.
The loop count is read from the multiplier stack and every copied bit is paid. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ScaleData := SubexponentialSAT.StructuredProgram.State 3 6

def scaleInvariant (base : ScaleData) (count : ℕ) (i : ℕ) (d : ScaleData) : Prop :=
  d.stacks 1 = List.replicate count false ∧
  d.stacks 2 = List.replicate (i*count) false ++ base.stacks 2 ∧
  d.stacks 5 = [] ∧
  (∀ j : Fin 6, j ≠ 2 → j ≠ 3 → j ≠ 4 → d.stacks j = base.stacks j)

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed binary computation of the reciprocal-error packing coefficients.
Sources 0..3 hold n,s,M,r. Outputs 4,5 hold n²s² and 8M²r².
Ports 6,7 and 8..12 are temporary products and arithmetic scratch. -/
namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

theorem shift_eval (d : Data) : Eval shift 6 d (shifted d) := by
  let a := SubexponentialSAT.Subexp.TupleProgram.pushedState 5 0 false d
  let b := SubexponentialSAT.Subexp.TupleProgram.pushedState 5 0 false a
  have h := (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval 5 0 false d).seq
    ((SubexponentialSAT.Subexp.TupleProgram.pushConst_eval 5 0 false a).seq
      (SubexponentialSAT.Subexp.TupleProgram.pushConst_eval 5 0 false b))
  simpa [shift, shifted, a, b, SubexponentialSAT.Subexp.TupleProgram.pushedState] using h

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWeightProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

/-- The two output words are binary; the initial sources and every other stack
are preserved. Arithmetic is valid even when an input denotes zero. -/
theorem command_eval (d : Data) (hd : ready d) :
    ∃ t ≤ 500 * (2 * inputLength d + 4)^2, ∃ e : Data,
      Eval command t d e ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 4) = incidence d ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 5) = head d ∧
      (e.stacks 4).length ≤ 2 * (d.stacks 0).length + 2 * (d.stacks 1).length + 3 ∧
      (e.stacks 5).length ≤ 2 * (d.stacks 2).length + 2 * (d.stacks 3).length + 6 ∧
      (∀ j, j ≠ 4 → j ≠ 5 → e.stacks j = d.stacks j) := by
  have hv0 : Valid (ports 0) d := by
    constructor
    · exact hd 6 (by decide)
    · intro i; exact hd (work i) (by fin_cases i <;> decide)
  obtain ⟨t₀, r₀, w₀, he₀, hv₀, hl₀, ht₀⟩ := multiplyAt_eval (ports 0) d hv0
  let d₁ : Data := ⟨r₀, Function.update d.stacks 6 w₀⟩
  have hv1 : Valid (ports 1) d₁ := by
    constructor
    · simpa [d₁, ports] using hd 4 (by decide)
    · intro i
      have hi : work i ≠ 6 := (ports 0).work_ne_out i
      simpa [d₁, ports, hi] using hv0.2 i
  obtain ⟨t₁, r₁, w₁, he₁, hv₁, hl₁, ht₁⟩ := multiplyAt_eval (ports 1) d₁ hv1
  let d₂ : Data := ⟨r₁, Function.update d₁.stacks 4 w₁⟩
  have hv2 : Valid (ports 2) d₂ := by
    constructor
    · simpa [d₂, d₁, ports] using hd 7 (by decide)
    · intro i
      have hi : work i ≠ 4 := (ports 1).work_ne_out i
      simpa [d₂, ports, hi] using hv1.2 i
  obtain ⟨t₂, r₂, w₂, he₂, hv₂, hl₂, ht₂⟩ := multiplyAt_eval (ports 2) d₂ hv2
  let d₃ : Data := ⟨r₂, Function.update d₂.stacks 7 w₂⟩
  have hv3 : Valid (ports 3) d₃ := by
    constructor
    · simpa [d₃, d₂, d₁, ports] using hd 5 (by decide)
    · intro i
      have hi : work i ≠ 7 := (ports 2).work_ne_out i
      simpa [d₃, ports, hi] using hv2.2 i
  obtain ⟨t₃, r₃, w₃, he₃, hv₃, hl₃, ht₃⟩ := multiplyAt_eval (ports 3) d₃ hv3
  let d₄ : Data := ⟨r₃, Function.update d₃.stacks 5 w₃⟩
  let d₅ := shifted d₄
  let d₆ := cleared d₅ 6
  let e := cleared d₆ 7
  have hs := shift_eval d₄
  have hc6 := clear_eval d₅ 6
  have hc7 := clear_eval d₆ 7
  have hl0 : w₀.length ≤ (d.stacks 0).length + (d.stacks 1).length + 1 := hl₀
  have hl1 : w₁.length ≤ 2 * w₀.length + 1 := by simpa [d₁, ports, two_mul] using hl₁
  have hl2 : w₂.length ≤ (d.stacks 2).length + (d.stacks 3).length + 1 := by
    simpa [d₂, d₁, ports] using hl₂
  have hl3 : w₃.length ≤ 2 * w₂.length + 1 := by simpa [d₃, ports, two_mul] using hl₃
  have htime0 : t₀ ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht₀.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    dsimp [ports, inputLength]; omega
  have htime1 : t₁ ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht₁.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp only [ports, Matrix.cons_val_one, Matrix.cons_val_zero, d₁,
      Function.update_self]
    dsimp [inputLength]; omega
  have htime2 : t₂ ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht₂.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [ports, d₂, d₁, inputLength]; omega
  have htime3 : t₃ ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht₃.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [ports, d₃, inputLength]; omega
  have hlen6 : (d₅.stacks 6).length = w₀.length := by
    simp [d₅, shifted, d₄, d₃, d₂, d₁]
  have hlen7 : (d₆.stacks 7).length = w₂.length := by
    simp [d₆, cleared, d₅, shifted, d₄, d₃]
  refine ⟨t₀ + (t₁ + (t₂ + (t₃ + (6 +
    ((2 * (d₅.stacks 6).length + 3) + (2 * (d₆.stacks 7).length + 3)))))),
    ?_, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen6, hlen7]
    have hsum : w₀.length + w₂.length ≤ inputLength d + 2 := by
      dsimp [inputLength]; omega
    nlinarith only [hsum, htime0, htime1, htime2, htime3]
  · exact he₀.seq (he₁.seq (he₂.seq (he₃.seq (hs.seq (hc6.seq hc7)))))
  · simp [e, d₆, cleared, d₅, shifted, d₄, d₃, d₂]
    simp [ports] at hv₀
    simp [ports, d₁] at hv₁
    rw [hv₁, hv₀]
    dsimp [incidence]
    ring
  · simp [e, d₆, cleared, d₅, shifted, d₄]
    simp [ports, d₂, d₁] at hv₂
    simp [ports, d₃] at hv₃
    rw [hv₃, hv₂]
    dsimp [head]
    ring
  · simp [e, d₆, cleared, d₅, shifted, d₄, d₃, d₂]
    omega
  · simp [e, d₆, cleared, d₅, shifted, d₄]
    omega
  · intro j hj4 hj5
    by_cases hj6 : j = 6
    · subst j; simp [e, d₆, cleared, hd 6 (by decide)]
    by_cases hj7 : j = 7
    · subst j; simp [e, cleared, hd 7 (by decide)]
    simp [e, d₆, cleared, d₅, shifted, d₄, d₃, d₂, d₁, hj4, hj5, hj6, hj7]

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramPrepend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive emission of a key/coefficient record. Both source words
are reversed; all bits, framing tags and source cleanup are executed. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def prependData (regs : Fin 3 → Bool) (key coeff output : List Bool) : State 3 3 :=
  ⟨regs, ![key,coeff,output]⟩

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramNat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive unary-field reader used by encoded sparse-key joins.
The unary magnitude affects execution time, never the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def afterNat {s : ℕ} (d : State 5 s) (src dst : Fin s) (n : ℕ) (rest : List Bool) : State 5 s :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst
      (List.replicate n true ++ d.stacks dst)⟩

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def afterFrame8 {s : ℕ} (d : State 8 s) (src dst : Fin s) (bits : List Bool) (rest : List Bool) : State 8 s :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst
      (bits.reverse ++ d.stacks dst)⟩

def afterTransfer8 {s : ℕ} (d : State 8 s) (src dst : Fin s) : State 8 s :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

def readRecordResult (d : State 8 28) (key coeff tail : List Bool) : State 8 28 :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update (Function.update (Function.update d.stacks
      27 tail) 16 key.reverse) 18 []) 17 coeff⟩

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed16/256 frame primitives for beta evaluation. These use the immutable
reader and transfer programs and are independent of the larger moment driver. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaFrames
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev Data := State 16 256
abbrev afterTransfer (d : Data) (src dst : Fin 256) : Data :=
  ⟨readRegs d.regs 0 1 none, transferStacks src dst d.stacks⟩

abbrev afterFrame (d : Data) (src dst : Fin 256) (bits tail : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src tail) dst (bits.reverse ++ d.stacks dst)⟩

end SubexponentialSAT.SqrtLog.PerturbationBetaFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native beta evaluation.  The caller supplies actual coefficient arrays,
not evaluated row values.  Masters205..212 are preserved;220 is the result.
Work230/231/232 holds the framed row scan, choice scan and reverse buffer. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives

abbrev Data := State 16 256

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyRelStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-call source witnesses suffice for a valid typed payload and its exact
incidence semantics. No common byte representation across source calls is
required. Length transports below only identify equal ambient dimensions. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly

open SubexponentialSAT DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

noncomputable def castJet {R : Type*} [CommRing R] {m n : ℕ}
    (h : m=n) (P : Squarefree.Jet (Fin m) R) : Squarefree.Jet (Fin n) R := h ▸ P

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramEntriesEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual signed-pair framing, with every unrelated stack preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev EmitData := State 3 6

def emitOneStacks (negative : Bool) (d : EmitData) : Fin 6 → List Bool :=
  Function.update (Function.update d.stacks (if negative then 1 else 0) []) 2
    (true :: (Encoding.frame (d.stacks (if negative then 1 else 0)).reverse ++ d.stacks 2))

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpInputZip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical pairing of row and input-coordinate streams

Two ordinary framed lists are read on stacks 0 and 1. The fixed program builds
the exact paired-record stream consumed by `SubexpDotControl`, on stack 6.
No array lookup, pairing, or serialization is a semantic machine instruction.
-/

namespace SubexponentialSAT.SubexpInputZip

open BitProgram StructuredCalls SubexpScanPrimitives

theorem writer_data_eval (d : Data) (bits : List Bool)
    (hs : d.stacks 7 = bits.reverse) :
    Eval writer (5 * bits.length + 7) d (afterWriter d bits) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks 0) (d.stacks 1) (d.stacks 4) bits.reverse
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 0) (d.stacks 1) (true :: (Encoding.frame bits ++ d.stacks 4)) []
  have ha : embedState regPorts writerPorts d a = d := by
    apply embedState_eq _ _ regPorts_injective writerPorts_injective
    · intro i; fin_cases i <;> rfl
    · intro i
      fin_cases i <;> simp [a, writerPorts, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, hs]
    · intros; rfl
    · intros; rfl
  have hb : embedState regPorts writerPorts d b = afterWriter d bits := by
    apply embedState_eq _ _ regPorts_injective writerPorts_injective
    · intro i
      fin_cases i <;> simp [afterWriter, finishedRegs, regPorts, b,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.triple]
    · intro i
      fin_cases i <;> simp [afterWriter, writerPorts, b,
        SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
      simp [afterWriter, finishedRegs, h0, h1]
    · intro i hi
      have h7 : i ≠ 7 := fun h => hi ⟨3, h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨2, h.symm⟩
      simp [afterWriter, h7, h4]
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 0) (d.stacks 1)
    (d.stacks 4) (d.regs 0) (d.regs 1) (d.regs 2)
  have h := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram regPorts writerPorts d
    regPorts_injective writerPorts_injective ht
  change Eval _ _ (embedState _ _ d a) (embedState _ _ d b) at h
  simpa only [writer, ha, hb] using h

theorem writer_eval (regs : Fin 8 → Bool)
    (row input left right pair acc output bits : List Bool) :
    Eval writer (5 * bits.length + 7)
      (state regs row input left right pair acc output bits)
      (state (finishedRegs regs) row input left right
        (true :: (Encoding.frame bits.reverse ++ pair)) acc output []) := by
  have h := writer_data_eval (state regs row input left right pair acc output bits) bits.reverse
    (by simp [])
  have he : afterWriter (state regs row input left right pair acc output bits) bits.reverse =
      state (finishedRegs regs) row input left right
        (true :: (Encoding.frame bits.reverse ++ pair)) acc output [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  simpa only [he, List.length_reverse] using h

theorem pair_execute (regs : Fin 8 → Bool)
    (left right rowTail inputTail acc output : List Bool) :
    ∃ rf, Eval pairCommand (20 * left.length + 20 * right.length + 41)
      (ready regs (Encoding.frame left ++ rowTail) (Encoding.frame right ++ inputTail) acc output)
      (ready rf rowTail inputTail ((record left right).reverse ++ acc) output) := by
  let d := ready regs (Encoding.frame left ++ rowTail) (Encoding.frame right ++ inputTail) acc output
  obtain ⟨e₁, h₁, hs₁⟩ := SubexpInputFrames.readField_execute 0 2 (by decide) d left rowTail rfl rfl
  have he₁ : e₁ = state e₁.regs rowTail (Encoding.frame right ++ inputTail)
      left.reverse [] [] acc output [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs₁]; first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨e₂, h₂, hs₂⟩ := SubexpInputFrames.readField_execute 1 3 (by decide)
    e₁ right inputTail (by rw [he₁]; rfl) (by rw [he₁]; rfl)
  have he₂ : e₂ = state e₂.regs rowTail inputTail left.reverse right.reverse [] acc output [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs₂, he₁]; first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [he₁] at h₁ h₂
  rw [he₂] at h₂
  let r₃ := readRegs e₂.regs 0 1 none
  let r₄ := finishedRegs r₃
  let r₅ := readRegs r₄ 0 1 (some true)
  let r₆ := readRegs r₅ 0 1 none
  let r₇ := finishedRegs r₆
  have h₃ := move_right e₂.regs rowTail inputTail left.reverse right.reverse [] acc output
  simp only [List.length_reverse, List.reverse_reverse] at h₃
  have h₄ := writer_eval r₃ rowTail inputTail left.reverse [] [] acc output right
  simp only [List.append_nil] at h₄
  have h₅ := popPair_eval r₄ rowTail inputTail left.reverse [] (Encoding.frame right.reverse) acc output []
  have h₆ := move_left r₅ rowTail inputTail left.reverse [] (Encoding.frame right.reverse) acc output
  simp only [List.length_reverse, List.reverse_reverse] at h₆
  have h₇ := writer_eval r₆ rowTail inputTail [] [] (Encoding.frame right.reverse) acc output left
  have h₈ := move_pair r₇ rowTail inputTail [] [] (record left right) acc output
  rw [record_length] at h₈
  have h := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃ (Eval.seq h₄
    (Eval.seq h₅ (Eval.seq h₆ (Eval.seq h₇ h₈))))))
  refine ⟨readRegs r₇ 0 1 none, ?_⟩
  have hc : 6 * left.length + 4 + (6 * right.length + 4 +
      (3 * right.length + 3 + (5 * right.length + 7 + (1 +
        (3 * left.length + 3 + (5 * left.length + 7 +
          (3 * (2 * left.length + 2 * right.length + 3) + 3))))))) =
      20 * left.length + 20 * right.length + 41 := by omega
  simpa only [pairCommand, hc] using h

theorem loop_execute (pairs : List (List Bool × List Bool)) (regs : Fin 8 → Bool)
    (rowSuffix inputSuffix acc output : List Bool)
    (hf : regs 7 = SubexpDotControl.listFlag pairs) :
    ∃ rf, Eval loop (scanCost pairs)
      (ready regs (rowAfter pairs rowSuffix) (inputAfter pairs inputSuffix) acc output)
      (ready rf rowSuffix inputSuffix ((pairBody pairs).reverse ++ acc) output) := by
  induction pairs generalizing regs acc with
  | nil =>
    refine ⟨regs, ?_⟩
    have h : Eval loop 1 (ready regs rowSuffix inputSuffix acc output)
        (ready regs rowSuffix inputSuffix acc output) := .while_false hf
    simpa only [scanCost, rowAfter, inputAfter, pairBody, List.reverse_nil, List.nil_append]
      using h
  | cons pair rest ih =>
    rcases pair with ⟨left, right⟩
    obtain ⟨rp, hp⟩ := pair_execute regs left right
      (Encoding.encodeList id (rowWords rest) ++ rowSuffix)
      (Encoding.encodeList id (inputWords rest) ++ inputSuffix) acc output
    obtain ⟨rt, ht, hft⟩ := tags_execute rp (SubexpDotControl.listFlag rest)
      (rowAfter rest rowSuffix) (inputAfter rest inputSuffix) ((record left right).reverse ++ acc) output
    rw [← row_tag, ← input_tag] at ht
    obtain ⟨rf, htail⟩ := ih rt ((record left right).reverse ++ acc) hft
    refine ⟨rf, ?_⟩
    have h := Eval.while_true hf (Eval.seq hp ht) htail
    simpa only [loop, scanCost, rowAfter, inputAfter, pairBody, List.reverse_append,
      List.append_assoc, show 20 * left.length + 20 * right.length + 41 + 2 + scanCost rest + 1 =
        20 * left.length + 20 * right.length + 44 + scanCost rest by omega] using h

theorem program_trace (pairs : List (List Bool × List Bool)) (regs : Fin 8 → Bool)
    (rowSuffix inputSuffix outputSuffix : List Bool) :
    ∃ rf, Trace program (26 * inputBits pairs + 53 * pairs.length + 12)
      ((ready regs (Encoding.encodeList id (rowWords pairs) ++ rowSuffix)
        (Encoding.encodeList id (inputWords pairs) ++ inputSuffix) [] outputSuffix).withPC
          (some program.entry))
      ((ready rf rowSuffix inputSuffix []
        (SubexpDotControl.encodePairs id pairs ++ outputSuffix)).withPC none) := by
  obtain ⟨rt, ht, hft⟩ := tags_execute regs (SubexpDotControl.listFlag pairs)
    (rowAfter pairs rowSuffix) (inputAfter pairs inputSuffix) [] outputSuffix
  rw [← row_tag, ← input_tag] at ht
  obtain ⟨rl, hl⟩ := loop_execute pairs rt rowSuffix inputSuffix [] outputSuffix hft
  simp only [List.append_nil] at hl
  obtain ⟨rf, hf⟩ := finish_execute rl rowSuffix inputSuffix (pairBody pairs).reverse outputSuffix
  simp only [List.length_reverse, List.reverse_reverse, pairBody_encodePairs] at hf
  have h := compiled_halt_trace (Eval.seq ht (Eval.seq hl hf)) 0 6
  refine ⟨rf, ?_⟩
  have hc : 2 + (scanCost pairs + (3 * (pairBody pairs).length + 8)) + 1 =
      26 * inputBits pairs + 53 * pairs.length + 12 := by
    rw [scanCost_eq, pairBody_length]
    omega
  simpa only [program, command, hc] using h

end SubexponentialSAT.SubexpInputZip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Small, extensional frame facts for the row interpreter. These proofs
split only its four control ports; they never enumerate the 256-stack frame. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram StructuredCalls
open SubexpPostfixGlobal (reindexCfg)
open SubexpPostfixInterpreter (cfg)

def contextStore (context : Fin 252 → List Bool) : Fin 256 → List Bool :=
  (physicalCfg (l := 1) none false false false [] [] [] context).stacks

end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical initialization of the sequential assignment memory

The input contains the already generated alphabet and incidence records.
This fixed routine duplicates the runtime tables, creates the initial packed
assignment by actual repeated copying, and clears all temporary ports. The
production of the input records is a separate frontend stage.
-/

namespace SubexponentialSAT.Subexp.AssignmentInitProgram

open BitProgram StructuredCalls StackRoutines

theorem reset_eval (d : Data) :
    Eval reset 16 d ⟨fun _ => false, d.stacks⟩ := by
  have h := SequentialProgram.resetList_eval (List.finRange 16) d
  simpa [reset, SequentialProgram.resetState] using h

theorem repeatDefault_eval (ctx : Context) :
    Eval repeatDefault (ctx.seedCount * (7 * ctx.defaultWord.length + 7) + 3)
      (state ctx (fun _ => false) ctx.defaultWord [] (unary ctx.seedCount)
        (unary ctx.seedCount) [])
      (state ctx (fun _ => false) ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord)
        (unary ctx.seedCount) [] []) := by
  let before := state ctx (fun _ => false) ctx.defaultWord []
    (unary ctx.seedCount) (unary ctx.seedCount) []
  let after := state ctx (fun _ => false) ctx.defaultWord
    (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) [] []
  have hin : embedState copyRegisters copyPorts before
      (BlockCopyProgram.initialState ctx.seedCount ctx.defaultWord []) = before := by
    apply embedState_eq_of_ports _ _ _ _ _ copyRegisters_injective copyPorts_injective
    · intro i; fin_cases i <;> simp [before, state, copyRegisters,
        BlockCopyProgram.initialState, BlockCopyProgram.data]
    · intros; rfl
    · intro i; fin_cases i <;> simp [before, state, copyPorts, unary,
        BlockCopyProgram.initialState, BlockCopyProgram.data]
    · intros; rfl
  have hout : embedState copyRegisters copyPorts before
      (BlockCopyProgram.data false false ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord ++ []) []) = after := by
    apply embedState_eq_of_ports _ _ _ _ _ copyRegisters_injective copyPorts_injective
    · intro i; fin_cases i <;> simp [after, state, copyRegisters, BlockCopyProgram.data]
    · intros; rfl
    · intro i; fin_cases i <;> simp [after, state, copyPorts, BlockCopyProgram.data]
    · intro j hj
      have h2 : j ≠ 2 := fun h => hj ⟨3, by simpa [copyPorts] using h.symm⟩
      have h8 : j ≠ 8 := fun h => hj ⟨1, by simpa [copyPorts] using h.symm⟩
      simp [before, after, state, h2, h8]
  have h := eval_call_lifted BlockCopyProgram.program copyRegisters copyPorts before
    copyRegisters_injective copyPorts_injective
    (BlockCopyProgram.program_trace ctx.seedCount ctx.defaultWord [])
  simpa only [hin, hout, repeatDefault, before, after] using h

theorem clearDefault_eval (ctx : Context) :
    Eval clearDefault (2 * ctx.defaultWord.length + 3)
      (state ctx (fun _ => false) ctx.defaultWord
        (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) []
        ctx.alphabetRecords)
      (outputState ctx) := by
  have h := TupleProgram.clear_eval (0 : Fin 48) (0 : Fin 16) 1
    (state ctx (fun _ => false) ctx.defaultWord
      (BlockCopyProgram.copies ctx.seedCount ctx.defaultWord) (unary ctx.seedCount) []
      ctx.alphabetRecords)
  convert h using 1
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> simp [state, readRegs]
    · funext j; fin_cases j <;> simp [state, clearStacks]

theorem command_eval (ctx : Context) (regs : Fin 16 → Bool) :
    Eval command (sourceCost ctx - 1) (inputState ctx regs) (outputState ctx) := by
  have hr := reset_eval (inputState ctx regs)
  have he := hr.seq ((copyRemaining_eval ctx).seq ((copyCounter_eval ctx).seq
    ((repeatDefault_eval ctx).seq ((copyAlphabet_eval ctx).seq (clearDefault_eval ctx)))))
  convert he using 1 ; simp [sourceCost, Nat.mul_add] ; omega

theorem program_trace (ctx : Context) (regs : Fin 16 → Bool) :
    Trace program (sourceCost ctx)
      ((inputState ctx regs).withPC (some program.entry))
      ((outputState ctx).withPC none) := by
  have ht := compiled_halt_trace (command_eval ctx regs) 0 8
  have hp : 1 ≤ sourceCost ctx := by unfold sourceCost; omega
  simpa [program, Nat.sub_add_cancel hp] using ht

end SubexponentialSAT.Subexp.AssignmentInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One-output physical calls in the assignment-input workspace. -/

namespace SubexponentialSAT.Subexp.AssignmentInputCall

open BitProgram StructuredCalls SubexpSetupStorage

theorem beforeCopies_stacks (a : Data) (hc : Clean a) :
    (beforeCopies 31 work a).stacks = a.stacks := by
  funext j
  simp only [beforeCopies, resetMany_stacks, clearMany_stacks]
  by_cases hw : j ∈ work
  · simp [hw, hc.1 j hw]
  · by_cases he : j = 31
    · subst j; simp [hw, hc.2]
    · simp [hw, he]

theorem prepare_one_stacks (a : Data) (hc : Clean a) (src dst : Fin 48)
    (hd : dst ∈ work) :
    (prepareState 31 work [(src, dst)] a).stacks =
      Function.update a.stacks dst (a.stacks src) := by
  simp [prepareState, copyManyState, copyState_stack, beforeCopies_stacks a hc,
    hc.1 dst hd]

theorem prepare_two_stacks (a : Data) (hc : Clean a) (src dst src' dst' : Fin 48)
    (hd : dst ∈ work) (hd' : dst' ∈ work) (hdd : dst' ≠ dst) (hsd : src' ≠ dst) :
    (prepareState 31 work [(src, dst), (src', dst')] a).stacks =
      Function.update (Function.update a.stacks dst (a.stacks src)) dst' (a.stacks src') := by
  simp [prepareState, copyManyState, copyState_stack, beforeCopies_stacks a hc,
    hc.1 dst hd, hc.1 dst' hd', hdd, hsd]

theorem prepare_one_local {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (a : Data) (hc : Clean a) (src : Fin 48) (q : Fin s) (i : Fin s) :
    (project (register hr) (stack hs) (prepareState 31 work [(src, stack hs q)] a)).stacks i =
      if i = q then a.stacks src else [] := by
  change (prepareState 31 work [(src, stack hs q)] a).stacks (stack hs i) = _
  rw [prepare_one_stacks a hc src (stack hs q) (stack_mem hs q)]
  by_cases he : i = q
  · subst i; simp
  · have hne := fun h => he (stack_injective hs h)
    rw [Function.update_of_ne hne]
    simp [he, hc.1 _ (stack_mem hs i)]

theorem prepare_two_local {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (a : Data) (hc : Clean a) (src src' : Fin 48) (q q' : Fin s)
    (hqq : q' ≠ q) (hsrc : src' ≠ stack hs q) (i : Fin s) :
    (project (register hr) (stack hs)
      (prepareState 31 work [(src, stack hs q), (src', stack hs q')] a)).stacks i =
      if i = q' then a.stacks src' else if i = q then a.stacks src else [] := by
  change (prepareState 31 work [(src, stack hs q), (src', stack hs q')] a).stacks
    (stack hs i) = _
  rw [prepare_two_stacks a hc src (stack hs q) src' (stack hs q')
    (stack_mem hs q) (stack_mem hs q') (fun h => hqq (stack_injective hs h)) hsrc]
  by_cases he' : i = q'
  · subst i; simp
  · have hne' := fun h => he' (stack_injective hs h)
    by_cases he : i = q
    · subst i
      rw [Function.update_of_ne hne']
      simp [he']
    · have hne := fun h => he (stack_injective hs h)
      rw [Function.update_of_ne hne', Function.update_of_ne hne]
      simp [he, he', hc.1 _ (stack_mem hs i)]

theorem prepare_frame (inputs : List (Fin 48 × Fin 48)) (a : Data)
    (hin : ∀ p ∈ inputs, p.2 ∈ work) (hc : Clean a) (j : Fin 48) (hj : j ∉ work) :
    (prepareState 31 work inputs a).stacks j = a.stacks j := by
  rw [prepareState, copyMany_frame inputs _ j]
  · simp only [beforeCopies, resetMany_stacks, clearMany_stacks, ite_eq_right hj]
    by_cases he : j = 31
    · subst j
      simp [hc.2]
    · simp [he]
  · intro p hp he
    exact hj (he.symm ▸ hin p hp)

theorem finish_one_stacks {r s : ℕ} (hr : r ≤ 16) (hs : s ≤ 10)
    (inputs : List (Fin 48 × Fin 48)) (a : Data) (out : State r s)
    (q : Fin s) (dst : Fin 48) (hd : dst ∉ work)
    (hin : ∀ p ∈ inputs, p.2 ∈ work) (hc : Clean a) :
    (finishState work [(stack hs q, dst)]
      (embedState (register hr) (stack hs) (prepareState 31 work inputs a) out)).stacks =
        Function.update a.stacks dst (out.stacks q) := by
  let middle := embedState (register hr) (stack hs) (prepareState 31 work inputs a) out
  have hqd : stack hs q ≠ dst := by
    intro he
    exact hd (he ▸ stack_mem hs q)
  have hq : middle.stacks (stack hs q) = out.stacks q :=
    embedState_stack _ _ _ _ (stack_injective hs) q
  funext j
  have hform : (finishState work [(stack hs q, dst)] middle).stacks j =
      if j ∈ work then [] else if j = dst then middle.stacks (stack hs q) else middle.stacks j := by
    by_cases he : j = dst <;>
      simp [finishState, resetMany_stacks, clearMany_stacks, copyManyState, copyState,
        StackRoutines.copyStacks, hqd, he]
  rw [hform]
  by_cases hw : j ∈ work
  · have hne : j ≠ dst := by intro he; exact hd (he ▸ hw)
    simp [hw, hne, hc.1 j hw]
  · have hf : middle.stacks j = a.stacks j := by
      rw [embedState_stack_frame]
      · exact prepare_frame inputs a hin hc j hw
      · rintro ⟨i, rfl⟩
        exact hw (stack_mem hs i)
    simp [hw, hf, hq, Function.update_apply]

theorem clearMany_bound (ports : List (Fin 48)) (a : Data) (B : ℕ) (h : Within a B) :
    Within (clearManyState ports a) B ∧ clearManyCost ports a ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing a with
  | nil => exact ⟨h, by simp [clearManyCost]⟩
  | cons p ps ih =>
      obtain ⟨hs, ht⟩ := ih (clearState p a) (within_clear p a B h)
      refine ⟨hs, ?_⟩
      have hp := h p
      simp only [clearManyCost, List.length_cons]
      nlinarith

end SubexponentialSAT.Subexp.AssignmentInputCall

end OAI.Algorithms
end


