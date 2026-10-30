-- Prove2me | Definitions.Def_OAIQ081S057
-- name    : OAIQ081S057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:46:30.955488+00:00
-- url     : https://prove2.me/theorems/419c77ee-4a11-43b1-95b6-8ff77d76979e
-- title:
--   Definitions bundle OAIQ081S057 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 108 declarations of OpenAI's Lean: 62 definitions and 46 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.packedValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.readSignedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.Head`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.U`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.depth`, `OAI.Algorithms.SubexponentialSAT.Subexp.BucketProgram.loopBudget`, `OAI.Algorithms.SubexponentialSAT.Subexp.BucketProgram.ready`, `OAI.Algorithms.SubexponentialSAT.Subexp.BucketProgram.scanOutput`, `OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram.Ready`, `OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram.readCounterState`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.colorRows`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.initializeList`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.lookup`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.markDifferent`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.ports`, `OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanProgram.selectedPositions`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketCalls.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingBucketTable.invariant`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingCoveredQuery.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingCoveredQuery.budget`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingCoveredQuery.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.base`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.guard`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.ready`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingExtraction.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameCount.ready`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingFrameCount.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftoverEmitter.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftoverEmitter.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingLeftoverEmitter.workState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingUnaryMin.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.Data`, `OAI.Algorithms.SubexponentialSAT.Subexp.SelectorProgram.ready`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactorLoop.ports` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramArrays`, `SubexponentialSAT_SqrtLog_LayoutProgramBlockCode`, `SubexponentialSAT_SqrtLog_LayoutProgramPadded`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarStep`, `SubexponentialSAT_SqrtLog_LayoutUniversal`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRun`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpNodeIndexProgram`, `SubexponentialSAT_SubexpRecordScan`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_BucketProgram`, `SubexponentialSAT_Subexp_DimensionProgram`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_MismatchPlanSpec`, `SubexponentialSAT_Subexp_PackingBucketCalls`, `SubexponentialSAT_Subexp_PackingBucketExecution`, `SubexponentialSAT_Subexp_PackingBucketSelect`, `SubexponentialSAT_Subexp_PackingBucketSemantics`, `SubexponentialSAT_Subexp_PackingBucketTable`, `SubexponentialSAT_Subexp_PackingExtractionBlock`, `SubexponentialSAT_Subexp_PackingExtractionOuter`, `SubexponentialSAT_Subexp_PackingExtractionSemantics`, `SubexponentialSAT_Subexp_PackingExtractionState`, `SubexponentialSAT_Subexp_PackingFrameCount`, `SubexponentialSAT_Subexp_PackingFrameSkip`, `SubexponentialSAT_Subexp_PackingLeftoverEmitter`, `SubexponentialSAT_Subexp_PackingUnaryMin`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_SelectorProgram`, `SubexponentialSAT_Subexp_UniversalRowExecution`, `SubexponentialSAT_Subexp_UniversalRowFactorLoop`, `SubexponentialSAT_Subexp_UniversalRowFactors`, `SubexponentialSAT_Subexp_UniversalRowGather`, `SubexponentialSAT_Subexp_UniversalRowGuard`, `SubexponentialSAT_Subexp_UniversalRowLoop`, `SubexponentialSAT_Subexp_UniversalRowMismatchTypes`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S035`, `OAIQ081S036` and `OAIQ081S040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S074`, `OAIQ081S075` and `OAIQ081S077`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.accumulate_eval_total` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S035
import Definitions.Def_OAIQ081S036
import Definitions.Def_OAIQ081S040

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramArrays
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical access to the two-array integer matrix ABI. Every array entry is a
runtime-width binary word; its signed value is positive minus negative. The
fixed program below preserves both arrays, the index and width. It does not
assume a unit-cost array lookup or add an integer primitive to the machine. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.ArrayUpdateLifted

def readSignedStacks (positive negative : List Bool)
    (stk : Stacks (Fin 11)) : Stacks (Fin 11) :=
  Function.update (Function.update stk 5 (positive ++ stk 5))
    6 (negative ++ stk 6)

@[simp] theorem readSignedStacks_positive (p n : List Bool)
    (stk : Stacks (Fin 11)) : readSignedStacks p n stk 5 = p ++ stk 5 := by
  simp [readSignedStacks]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramBlockCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Literal block-lookup and incidence-fiber circuits for the ring source rows.
The branches are exactly those implemented by the packing metadata lookup;
this file identifies their polynomial meanings without any field assumption. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.SubexpRowInterpolation
open LayoutPullback

variable {I U C O : Type*} [Fintype I] [DecidableEq I]
  [Fintype U] [DecidableEq U] [CommRing O]

noncomputable def packedValue (P : PackingData I U)
    (rows : U → U → Polynomial O) (v w : I) : Polynomial O :=
  match P.lookup v with
  | none => if w = v then 1 else 0
  | some (j,u) => match P.lookup w with
    | none => 0
    | some (k,y) => if j = k then rows u y else 0

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutUniversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual universal incidence-copy block over a commutative coefficient
ring in which the power-of-two denominator is a unit. -/

namespace SubexponentialSAT.SqrtLog.LayoutUniversal

open scoped BigOperators
open Matrix
open SubexponentialSAT.MulticolorTypes
open LayoutPullback LayoutExactBuckets LayoutScaledMatrices

variable {r Q : ℕ} {O : Type*} [CommRing O]

abbrev U (r Q : ℕ) := UniversalType r Q 1
abbrev Head (t : Fin Q) (g : Fin r) := {u : U r Q // u.head t = g}

end SubexponentialSAT.SqrtLog.LayoutUniversal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_DimensionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed generator for all unary dimensions from zero through a runtime bound

The input bound is a unary stack, and the output is a framed list of unary
payloads. The program has no bound-dependent control labels.
-/

namespace SubexponentialSAT.Subexp.DimensionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram

/-- Stack 0 is the remaining unary bound, stack 1 the current unary value,
stack 3 the accumulated framed records; stacks 2 and 4 are empty scratch. -/
def Ready (k : ℕ) (remaining : List Bool) (accum : Records) (a : State 5 5) : Prop :=
  a.stacks 0 = remaining ∧ a.stacks 1 = List.replicate k true ∧
  a.stacks 2 = [] ∧ a.stacks 3 = ProgramEncoding.encodeRecords accum ∧ a.stacks 4 = []

def readCounterState (a : State 5 5) : State 5 5 :=
  ⟨readRegs a.regs 0 1 (a.stacks 0).head?, Function.update a.stacks 0 (a.stacks 0).tail⟩

end SubexponentialSAT.Subexp.DimensionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPadded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A computable integer row for every incidence position. Inactive covered
positions and non-head uncovered positions are zero. Active rows are precisely
the raw block constraints, with repetitions and zero padding permitted. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q : ℕ} {I O : Type*}
variable [Fintype I] [DecidableEq I] [CommRing O]

/-- This definition uses the executable packing lookup and scalar numerator.
The arbitrary finite equivalence used by the semantic layout is absent. -/
def paddedEntry (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (v w : I) : ℤ :=
  match P.lookup v with
  | none => if (P.label v).head t = g ∧ w = v then 1 else 0
  | some (j,u) => match P.lookup w with
    | none => 0
    | some (k,y) =>
      if j = k ∧ u ∈ joint t g (0 : Fin 1) ∧ y ∈ joint t g (0 : Fin 1) then
        (if u = y then (2 : ℤ)^(R-1) else 0) -
          LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y
      else 0

end SubexponentialSAT.SqrtLog.LayoutProgram

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

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def wordTotal (x : WordPair) : ℕ := pairTotal x.1 x.2

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRecordScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control selection of serialized coefficient records

The inner record body is `frame key ++ frame coefficient`. All execution
claims below are traces of fixed Boolean-register/stack instruction tables.
-/

namespace SubexponentialSAT.SubexpRecordScan

open BitProgram StructuredProgram StructuredCalls

theorem twoPorts_injective (src dst : Fin 6) (h : src ≠ dst) :
    Function.Injective (twoPorts src dst) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [twoPorts, ParserProgram.pair]

def afterFrame (d : Data) (src dst : Fin 6) (bits rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst
      (bits.reverse ++ d.stacks dst)⟩

/-- The register/stack state after clearing a scratch port. -/
def afterClear (d : Data) (src : Fin 6) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

def afterCopy (d : Data) (src dst : Fin 6) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

theorem copy_eval (d : Data) (src dst tmp : Fin 6)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (htmp : d.stacks tmp = []) :
    StructuredCalls.Eval (.call (StackRoutines.copyProgram src dst tmp (0 : Fin 5) 1))
      (7 * (d.stacks src).length + 5) d (afterCopy d src dst) := by
  apply StructuredCalls.Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 5) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [afterCopy, StackRoutines.copyResult, StructuredProgram.State.withPC,
    StackRoutines.copyProgram, Nat.add_assoc] using hh

theorem skipRegs_injective : Function.Injective skipRegs := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [skipRegs, ExecCNFRecords.ports]

theorem payloadPorts_injective : Function.Injective payloadPorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [payloadPorts, ExecCNFRecords.ports]

def afterSkip (d : Data) (rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false), Function.update d.stacks 0 rest⟩

def afterPayload (d : Data) (bits rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 0 rest) 5
      (Encoding.frame bits ++ d.stacks 5)⟩

def selectedState (d : Data) (bits rest : List Bool) : Data :=
  if d.regs 4 then afterPayload d bits rest else afterSkip d rest

end SubexponentialSAT.SubexpRecordScan

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

theorem selected_append (xs ys : List Record) (query : List Bool) :
    selected (xs ++ ys) query = selected xs query ++ selected ys query := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨key, payload⟩
    by_cases h : key = query <;> simp [selected, h, ih]

theorem selected_reverse (rs : List Record) (query : List Bool) :
    selected rs.reverse query = (selected rs query).reverse := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨key, payload⟩
    by_cases h : key = query <;>
      simp [List.reverse_cons, selected_append, selected, h, ih]

def scanOutput (rs : List Record) (query output : List Bool) : List Bool :=
  frames (selected rs query).reverse ++ output

theorem scanOutput_cons (key payload : List Bool) (rs : List Record)
    (query output : List Bool) :
    scanOutput ((key, payload) :: rs) query output =
      scanOutput rs query (if key = query then Encoding.frame payload ++ output else output) := by
  by_cases h : key = query <;>
    simp [scanOutput, selected, h, frames_append, frames, List.append_assoc]

theorem scanOutput_reverse (rs : List Record) (query output : List Bool) :
    scanOutput rs.reverse query output = frames (selected rs query) ++ output := by
  simp [scanOutput, selected_reverse]

def ready (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) : Data :=
  recordState (readRegs regs 0 1 (encodeRecords rs).head?)
    (encodeRecords rs) [] query.reverse [] [] output

theorem peekInput_eval (regs : Fin 5 → Bool) (rs : List Record) (query output : List Bool) :
    StructuredCalls.Eval peekInput 1
      (recordState regs (encodeRecords rs) [] query.reverse [] [] output)
      (ready regs rs query output) := by
  exact StructuredCalls.Eval.base (StructuredProgram.Eval.atom _ _)

theorem ready_guard_nil (regs : Fin 5 → Bool) (query output : List Bool) :
    (ready regs [] query output).regs 1 = false := by
  simp [ready, encodeRecords, recordState, readRegs]

theorem ready_guard_cons (regs : Fin 5 → Bool) (key payload : List Bool)
    (rs : List Record) (query output : List Bool) :
    (ready regs ((key, payload) :: rs) query output).regs 1 = true := by
  cases key <;> simp [ready, encodeRecords, recordState, readRegs, Encoding.frame]

def loopBudget : List Record → List Bool → ℕ
  | [], _ => 1
  | (key, payload) :: rs, query => recordCost key query payload + 2 + loopBudget rs query

theorem record_count_le_length (rs : List Record) : rs.length ≤ (encodeRecords rs).length := by
  induction rs with
  | nil => simp [encodeRecords]
  | cons row rs ih =>
    rcases row with ⟨key, payload⟩
    simp only [encodeRecords, List.length_append, Encoding.length_frame, List.length_cons]
    omega

theorem loopBudget_le (rs : List Record) (query : List Bool) :
    loopBudget rs query ≤ 9 * (encodeRecords rs).length +
      rs.length * (9 * query.length + 20) + 1 := by
  induction rs with
  | nil => simp [loopBudget, encodeRecords]
  | cons row rs ih =>
    rcases row with ⟨key, payload⟩
    simp only [loopBudget, encodeRecords, List.length_append, Encoding.length_frame,
      List.length_cons, recordCost]
    nlinarith

section TypedBucket

variable {V U : Type*} [DecidableEq U]

theorem selected_vertexRecords (vertices : List V) (label : V → U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) (u : U) :
    selected (vertexRecords vertices label encodeType encodeVertex) (encodeType u) =
      (vertices.filter (fun v => decide (label v = u))).map encodeVertex := by
  induction vertices with
  | nil => rfl
  | cons v vs ih =>
    dsimp only [vertexRecords] at ih
    by_cases h : label v = u <;>
      simp [vertexRecords, selected, hinj.eq_iff, h, ih]

/-- The encoded output agrees exactly with the executable constructive bucket. -/
theorem constructive_bucket_output (P : ConstructivePacking.PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) (u : U) :
    selected (vertexRecords P.vertices.values P.label encodeType encodeVertex) (encodeType u) =
      (P.bucket u).map encodeVertex :=
  selected_vertexRecords P.vertices.values P.label encodeType encodeVertex hinj u

end TypedBucket

end SubexponentialSAT.Subexp.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrameCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame counter for the complete-block packing controller. -/

namespace SubexponentialSAT.Subexp.PackingFrameCount

open BitProgram StructuredCalls MatrixProgramSupport

abbrev state (regs : Fin 8 → Bool) (source payload count : List Bool) : StructuredProgram.State 8 3 :=
  ⟨regs, ![source, payload, count]⟩

abbrev ready (regs : Fin 8 → Bool) (source count : List Bool) : StructuredProgram.State 8 3 :=
  state (readRegs regs 0 1 source.head?) source [] count

theorem peek_eval (regs : Fin 8 → Bool) (source count : List Bool) :
    Eval peek 1 (state regs source [] count) (ready regs source count) := .base (.atom _ _)

theorem ready_nil (regs : Fin 8 → Bool) (count : List Bool) :
    (ready regs [] count).regs 1 = false := by simp [ readRegs]

theorem ready_cons (regs : Fin 8 → Bool) (bits source count : List Bool) :
    (ready regs (Encoding.frame bits ++ source) count).regs 1 = true := by
  cases bits <;> simp [ readRegs, Encoding.frame]

theorem budget_le (xs : List (List Bool)) : budget xs ≤ 11 * (words xs).length + 1 := by
  induction xs with
  | nil => simp [budget, words]
  | cons bits xs ih =>
    simp only [budget, List.map_cons, List.sum_cons] at *
    simp only [words, List.length_append, Encoding.length_frame]
    omega

end SubexponentialSAT.Subexp.PackingFrameCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingUnaryMin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed destructive minimum routine for unary packing counts. -/

namespace SubexponentialSAT.Subexp.PackingUnaryMin

open BitProgram StructuredCalls MatrixProgramSupport

def state (regs : Fin 8 → Bool) (left right output : List Bool) :
    StructuredProgram.State 8 3 :=
  ⟨regs, ![left, right, output]⟩

theorem core_nil (regs : Fin 8 → Bool) (right output : List Bool) :
    Trace core 4 ((state regs [] right output).withPC (some core.entry))
      ((state (popped regs none right.head?) [] right.tail output).withPC none) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, core, execInstr, state,
    StructuredProgram.State.withPC, popped, readRegs]
  all_goals (funext i; fin_cases i <;> simp)

theorem core_cons_nil (regs : Fin 8 → Bool) (bit : Bool) (left output : List Bool) :
    Trace core 5 ((state regs (bit :: left) [] output).withPC (some core.entry))
      ((state (popped regs (some bit) none) left [] output).withPC none) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, core, execInstr, state,
    StructuredProgram.State.withPC, popped, readRegs]
  all_goals (funext i; fin_cases i <;> simp)

theorem core_cons (regs : Fin 8 → Bool) (x y : Bool) (left right output : List Bool) :
    Trace core 7 ((state regs (x :: left) (y :: right) output).withPC (some core.entry))
      ((state (Function.update (popped regs (some x) (some y)) 0 true)
        left right (true :: output)).withPC (some core.entry)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, core, execInstr, state,
    StructuredProgram.State.withPC, popped, readRegs]
  all_goals (funext i; fin_cases i <;> simp)

theorem core_trace (left right output : List Bool) (regs : Fin 8 → Bool) :
    ∃ n ≤ 7 * min left.length right.length + 5, ∃ regs' left' right',
      Trace core n ((state regs left right output).withPC (some core.entry))
        ((state regs' left' right'
          (List.replicate (min left.length right.length) true ++ output)).withPC none) ∧
      left'.length ≤ left.length ∧ right'.length ≤ right.length := by
  induction left generalizing regs right output with
  | nil =>
    refine ⟨4, by simp, popped regs none right.head?, [], right.tail, ?_, by simp, ?_⟩
    · simpa using core_nil regs right output
    · simp
  | cons x left ih =>
    cases right with
    | nil =>
      refine ⟨5, by simp, popped regs (some x) none, left, [], ?_, by simp, by simp⟩
      simpa using core_cons_nil regs x left output
    | cons y right =>
      obtain ⟨n, hn, rf, ls, rs, ht, hl, hr⟩ := ih right (true :: output)
        (Function.update (popped regs (some x) (some y)) 0 true)
      have he := (core_cons regs x y left right output).trans ht
      have hm : min (x :: left).length (y :: right).length =
          min left.length right.length + 1 := by
        simp only [List.length_cons]
        omega
      have hout : List.replicate (min left.length right.length) true ++ true :: output =
          List.replicate (min (x :: left).length (y :: right).length) true ++ output := by
        rw [hm, List.replicate_add]
        simp [List.append_assoc]
      refine ⟨7 + n, by rw [hm]; omega,
        rf, ls, rs, ?_, by simpa using hl.trans (Nat.le_succ _),
        by simpa using hr.trans (Nat.le_succ _)⟩
      simpa only [hout] using he

end SubexponentialSAT.Subexp.PackingUnaryMin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-code lookup with fallback for local read plans

The table is a raw sequence of framed key/payload pairs. The query and table
are runtime bit strings. The program reuses the verified key comparison and
record parsing routines, retaining the first matching payload.
-/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev Data := SubexponentialSAT.SubexpRecordScan.Data

def ready (regs : Fin 5 → Bool) (records : List (List Bool × List Bool))
    (query : List Bool) : Data :=
  recordState (readRegs regs 0 1 (rawRecords records).head?)
    (rawRecords records) [] query.reverse [] [] []

theorem peek_eval (regs : Fin 5 → Bool) (input query output : List Bool) :
    Eval peek 1 (recordState regs input [] query [] [] output)
      (recordState (readRegs regs 0 1 input.head?) input [] query [] [] output) := by
  simpa [peek, atom, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, recordState]
    using (Eval.base (StructuredProgram.Eval.atom
      (StructuredProgram.Atom.peek (0 : Fin 6) (0 : Fin 5) 1)
      (recordState regs input [] query [] [] output)))

theorem stop_eval (regs : Fin 5 → Bool) (input query output : List Bool) :
    Eval (atom (.set 1 false)) 1 (recordState regs input [] query [] [] output)
      (recordState (Function.update regs 1 false) input [] query [] [] output) := by
  simpa [atom, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, recordState]
    using (Eval.base (StructuredProgram.Eval.atom
      (StructuredProgram.Atom.set (1 : Fin 5) false)
      (recordState regs input [] query [] [] output)))

theorem ready_nil_guard (regs : Fin 5 → Bool) (query : List Bool) :
    (ready regs [] query).regs 1 = false := by simp [ready, rawRecords, recordState, readRegs]

theorem ready_cons_guard (regs : Fin 5 → Bool) (key value query : List Bool)
    (records : List (List Bool × List Bool)) :
    (ready regs ((key, value) :: records) query).regs 1 = true := by
  cases key <;> simp [ready, rawRecords, Encoding.frame, recordState, readRegs]

end SubexponentialSAT.Subexp.SelectorProgram

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

theorem encodeRecords_eq_prefix (records : List (List Bool)) :
    ProgramEncoding.encodeRecords records = recordPrefix records ++ [false] := by
  induction records with
  | nil => rfl
  | cons bits records ih =>
      simp [ProgramEncoding.encodeRecords, Encoding.encodeList, recordPrefix,
        ProgramEncoding.encodeRecords] at ih ⊢
      rw [ih]

theorem fold_prepend (f : List Bool → List Bool) (queries : List (List Bool))
    (acc : List Bool) :
    queries.foldl (fun out query => TupleProgram.prependRecord (f query) out) acc =
      recordPrefix (queries.map f).reverse ++ acc := by
  induction queries generalizing acc with
  | nil => rfl
  | cons query queries ih =>
      rw [List.foldl_cons, ih]
      simp [recordPrefix, TupleProgram.prependRecord,
        List.reverse_cons, List.append_assoc]

end SubexponentialSAT.Subexp.SelectorMapProgram

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

abbrev Data := StructuredProgram.State 8 15

def state (regs : Fin 8 → Bool)
    (rows query bucket saved keys scan minimum table count result : List Bool) : Data :=
  ⟨regs, ![rows, [], query, [], [], bucket, saved, keys, [], scan,
    minimum, table, [], count, result]⟩

theorem frames_eq_words (xs : List (List Bool)) : BucketProgram.frames xs = words xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [BucketProgram.frames, words, ih]

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

theorem selected_length_le (records : List BucketProgram.Record) (key : List Bool) :
    (BucketProgram.selected records key).length ≤ records.length := by
  induction records with
  | nil => simp [BucketProgram.selected]
  | cons row rows ih =>
    rcases row with ⟨k, payload⟩
    by_cases hk : k = key <;> simp [BucketProgram.selected, hk] <;> omega

theorem selected_words_length_le (records : List BucketProgram.Record) (key : List Bool) :
    (words (BucketProgram.selected records key)).length ≤
      (BucketProgram.encodeRecords records).length := by
  induction records with
  | nil => simp [BucketProgram.selected, words, BucketProgram.encodeRecords]
  | cons row rows ih =>
    rcases row with ⟨k, payload⟩
    by_cases hk : k = key <;>
      simp [BucketProgram.selected, hk, words, BucketProgram.encodeRecords,
        Encoding.length_frame] <;> omega

theorem encodeRecords_length_reverse (records : List BucketProgram.Record) :
    (BucketProgram.encodeRecords records.reverse).length =
      (BucketProgram.encodeRecords records).length := by
  have hlen (xs : List BucketProgram.Record) :
      (BucketProgram.encodeRecords xs).length =
        (xs.map fun p => 2 * p.1.length + 2 * p.2.length + 2).sum := by
    induction xs with
    | nil => rfl
    | cons p xs ih =>
      rcases p with ⟨key, value⟩
      simp only [BucketProgram.encodeRecords, List.length_append, Encoding.length_frame,
        List.map_cons, List.sum_cons, ih]
      omega
  rw [hlen, List.map_reverse, List.sum_reverse, hlen]

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual all-type scan and minimum fold, preserving the supplied type order. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls MatrixProgramSupport PackingBucketCalls

def invariant (records : List BucketProgram.Record) (a : Data) : Prop :=
  a = state a.regs [] (a.stacks 2) [] (BucketProgram.encodeRecords records.reverse)
    (a.stacks 7) [] (List.replicate (a.stacks 10).length true) (a.stacks 11) [] [] ∧
  (a.stacks 10).length ≤ records.length

theorem invariant_state (records : List BucketProgram.Record) (regs : Fin 8 → Bool)
    (query keys acc : List Bool) (m : ℕ) (hm : m ≤ records.length) :
    invariant records (state regs [] query [] (BucketProgram.encodeRecords records.reverse)
      keys [] (List.replicate m true) acc [] []) := by
  constructor
  · simp [state]
  · simpa [state] using hm

def inputState (records : List BucketProgram.Record) (keys : List (List Bool))
    (initial : ℕ) (suffix : List Bool) (regs : Fin 8 → Bool) : Data :=
  state regs [] [] [] (BucketProgram.encodeRecords records.reverse)
    (ProgramEncoding.encodeRecords keys ++ suffix) [] (List.replicate initial true) [] [] []

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeIndexProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical lookup of the current field node

The fixed program copies the framed node table, parses its records in order,
compares their actual bits with the current node, and counts rejected records.
Its only visible stack change is the unary first matching index at port 116.
The source table at 125 and query at 78 are preserved.
-/

namespace SubexponentialSAT.SubexpNodeIndexProgram

open BitProgram StructuredCalls SubexpScanPrimitives

namespace Internal

abbrev clear (src : Fin 7) : Cmd 5 7 :=
  .call (StackRoutines.clearProgram src (0 : Fin 5) 1)

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured execution of the complete per-node setup, conditional only on
its explicit concrete integer-entry service. Uniform numerical resource bounds
are proved separately. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

abbrev CacheCorrect (height R width : List Bool) (words : List (List Bool)) : Prop :=
  words.length=R.length ∧ (∀ w∈words,w.length=width.length) ∧
    words.map SubexponentialSAT.BinaryArithmetic.toNat=
      (List.range R.length).map (LayoutCoefficientRecurrence.H height.length)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
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

local infixr:60 " ;; " => Cmd.seq

/-- Copy an already-framed literal without changing its coefficient encoding. -/
abbrev captureFrame : Cmd 3 8 :=
  .call (ProgramLinking.liftProgram
    { ExecCNFRecords.captureProgram with entry := 4 } registerMap (tripleMap 0 4 3))

abbrev emitFramedLiteral : Cmd 3 8 := atom (.set 0 false) ;; atom (.push 3 0) ;; captureFrame

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentInputProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

def depth : Code := copyMany 31 [(6, 34), (6, 34)]

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev lookup (right : Bool) : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id (lookupPorts right))

abbrev markDifferent : Cmd 8 16 :=
  .seq (RecordPrograms.atom (.pop 11 7 1)) (RecordPrograms.atom (.bnot 7 7))

def ports : RecordPrograms.Ports 8 16 where
  tag := 5
  present := 6
  found := 7
  source := 8
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev initializeList (dst : Fin 16) : Cmd 8 16 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.push dst 0))

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mismatch filter on the exact one-hot word representation. -/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls MulticolorTypes

def colorRows {r Q : ℕ} (w : MulticolorTypes.Word r Q) : List (List Bool) :=
  List.ofFn (fun i : Fin Q => oneHot (w i))

@[simp] theorem colorRows_length {r Q : ℕ} (w : MulticolorTypes.Word r Q) :
    (colorRows w).length = Q := by simp [colorRows]

@[simp] theorem colorRows_getD {r Q : ℕ} (w : MulticolorTypes.Word r Q) (i : Fin Q) :
    (colorRows w).getD i.val [] = oneHot (w i) := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [colorRows]

def selectedPositions {r Q : ℕ} (left right : MulticolorTypes.Word r Q) : List ℕ :=
  ((List.finRange Q).filter (fun i => decide (left i ≠ right i))).map Fin.val

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrameSkip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual framed-pre skip call with arbitrary surrounding packing data. -/

namespace SubexponentialSAT.Subexp.PackingFrameSkip

open BitProgram StructuredCalls MatrixProgramSupport

variable {s : ℕ}

theorem frames_eq_words (xs : List (List Bool)) : BlockZeroProgram.frames xs = words xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change Encoding.frame b ++ BlockZeroProgram.frames bs = Encoding.frame b ++ words bs
    rw [ih]

theorem cost_le (pre : List (List Bool)) :
    BlockZeroProgram.skipCost pre ≤ 4 * (words pre).length + 3 := by
  have hw := frames_eq_words pre
  simpa only [hw] using BlockZeroProgram.skipCost_le pre

end SubexponentialSAT.Subexp.PackingFrameSkip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketSelect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read one block's vertex from an actual serialized type bucket. -/

namespace SubexponentialSAT.Subexp.PackingBucketSelect

open BitProgram StructuredCalls MatrixProgramSupport

theorem words_append (xs ys : List (List Bool)) : words (xs ++ ys) = words xs ++ words ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [words, ih, List.append_assoc]

end SubexponentialSAT.Subexp.PackingBucketSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical bucket/minimum output is the existing computable packing. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open ConstructivePacking MatrixProgramSupport

variable {V U : Type*} [DecidableEq U]

theorem minimum_typed_aux (P : PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) (us : List U) (m : ℕ)
    (hm : m ≤ P.vertices.values.length) :
    minimum (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (us.map encodeType) m = min m (P.minCount us) := by
  induction us generalizing m with
  | nil => simp [minimum, PackingData.minCount, Nat.min_eq_left hm]
  | cons u us ih =>
    simp only [minimum, List.map_cons, List.foldl_cons]
    rw [BucketProgram.constructive_bucket_output P encodeType encodeVertex hinj,
      List.length_map]
    change minimum (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (us.map encodeType) (min m (P.bucket u).length) = _
    rw [ih _ ((min_le_left _ _).trans hm)]
    simp only [PackingData.minCount, Nat.min_assoc]

theorem minCount_le_vertices (P : PackingData V U) (us : List U) :
    P.minCount us ≤ P.vertices.values.length := by
  induction us with
  | nil => exact le_rfl
  | cons u us ih => exact (min_le_right _ _).trans ih

theorem minimum_eq_blockCount (P : PackingData V U)
    (encodeType : U → List Bool) (encodeVertex : V → List Bool)
    (hinj : Function.Injective encodeType) :
    minimum (BucketProgram.vertexRecords P.vertices.values P.label encodeType encodeVertex)
      (P.types.values.map encodeType) P.vertices.values.length = P.blockCount := by
  rw [minimum_typed_aux P encodeType encodeVertex hinj _ _ le_rfl]
  exact Nat.min_eq_right (minCount_le_vertices P P.types.values)

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical ports for block-major extraction and its bucket reader. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 19

def state (regs : Fin 8 → Bool) (c : Context)
    (source key count vertex scratch temp workA workB : List Bool) : Data :=
  ⟨regs, ![source, key, count, vertex, scratch, [], [], c.keys, c.payload, temp,
    c.block, c.address, c.storage, c.metadata, c.addresses, c.buckets, c.remaining,
    workA, workB]⟩

def ready (regs : Fin 8 → Bool) (c : Context) : Data := state regs c [] [] [] [] [] [] [] []

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionBlock
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scan the ordered type buckets for one complete block. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

def base (regs : Fin 8 → Bool) (c : Context) : Data :=
  ready regs { c with keys := [], payload := [] }

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed outer loop extracts all complete blocks in block-major order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

def guard (regs : Fin 8 → Bool) (c : Context) : Data :=
  base (readRegs regs 3 4 c.remaining.head?) c

theorem refresh_eval (regs : Fin 8 → Bool) (c : Context) :
    Eval refresh 1 (base regs c) (guard regs c) := .base (.atom _ _)

end SubexponentialSAT.Subexp.PackingExtraction

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

theorem emitEntries_storage (i : ℕ) (entries : List Entry) (c : Context) :
    (emitEntries i entries c).storage =
      (vertexPrefix (entries.map (entryVertex i))).reverse ++ c.storage := by
  induction entries generalizing c with
  | nil => simp [emitEntries, vertexPrefix]
  | cons e es ih =>
    change (emitEntries i es (emitted c e.1 (entryVertex i e))).storage = _
    rw [ih]
    simp [vertexPrefix, emitted, PackingEntryEmitter.storageOutput,
      List.reverse_append, List.append_assoc]

theorem advanceMany_storage (entries : List Entry) (n i : ℕ) (c : Context) :
    (advanceMany entries n i c).storage =
      (vertexPrefix (coverVertices entries n i)).reverse ++ c.storage := by
  induction n generalizing i c with
  | zero => simp [advanceMany, coverVertices, vertexPrefix]
  | succ n ih =>
    rw [advanceMany, ih]
    have hs : (advanced i entries c).storage = (emitEntries i entries c).storage := rfl
    rw [hs, emitEntries_storage]
    simp [coverVertices, vertexPrefix, List.range'_succ, List.flatMap_append,
      List.reverse_append, List.append_assoc]

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual emission and covered-key lookup for the leftover packing pass. -/
namespace SubexponentialSAT.Subexp.PackingLeftoverEmitter

open BitProgram StructuredCalls MatrixProgramSupport

abbrev Data := StructuredProgram.State 8 9

def workState (regs : Fin 8 → Bool)
    (vertex rank address storage metadata addresses scratch temp frame : List Bool) : Data :=
  ⟨regs, ![vertex,rank,address,storage,metadata,addresses,scratch,temp,frame]⟩

def state (regs : Fin 8 → Bool)
    (vertex rank address storage metadata addresses : List Bool) : Data :=
  workState regs vertex rank address storage metadata addresses [] [] []

end SubexponentialSAT.Subexp.PackingLeftoverEmitter

namespace SubexponentialSAT.Subexp.PackingCoveredQuery

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 5 6

def state (regs : Fin 5 → Bool) (source query output : List Bool) : Data :=
  SubexpRecordScan.recordState regs source [] query [] [] output

def budget (query : List Bool) (records : List (List Bool × List Bool)) : ℕ :=
  5*SelectorProgram.scanBudget query records +
    2*(SelectorProgram.rawRecords records).length+2*query.length+23

end SubexponentialSAT.Subexp.PackingCoveredQuery


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
open SubexpKernelControl (Word pushWord operator popTag emitFramedLiteral emitOperator countOne drain )

abbrev clearX : Cmd 3 8 := .call (StackRoutines.clearProgram (5 : Fin 8) (0 : Fin 3) 1)

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGather
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Reading actual scalar and difference-row data for universal rows

All tables are packed runtime arrays. The selected index is unary data on
stack 16. The three fixed reads preserve their source tables and index and
produce the correction scalar, inverse node, and complete difference row.
-/

namespace SubexponentialSAT.Subexp.UniversalRowGather

open BitProgram StructuredCalls StackRoutines

abbrev read (field : Field) : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 8) 1)
    id (readPorts field))

abbrev readIndex (field : Field) : Cmd 8 32 :=
  .seq (.call (copyProgram 16 2 15 (0 : Fin 8) 1)) (read field)

abbrev termFields : Cmd 8 32 :=
  .seq (readIndex .value) (.seq (readIndex .inverse) (readIndex .difference))

end SubexponentialSAT.Subexp.UniversalRowGather

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowFactors
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed array reads and framing for one interpolation factor. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactors

open BitProgram StructuredCalls
open UniversalRowGather (Word)

abbrev readAt (ports : Equiv.Perm (Fin 32)) : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram
    (compiled (UniversalRowGather.readIndex .value) 0 0) id ports)

abbrev readFactor : Cmd 8 32 := .seq (readAt differencePorts) (readAt negativePorts)

end SubexponentialSAT.Subexp.UniversalRowFactors

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

abbrev resetFlags : Cmd 8 32 :=
  .seq (RecordPrograms.atom (.set 5 false))
    (.seq (RecordPrograms.atom (.set 6 true)) (RecordPrograms.atom (.set 7 false)))

def ports : RecordPrograms.Ports 8 32 where
  tag := 5
  present := 6
  found := 7
  source := 8
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the actual mismatch-index records and compare their count with R. -/

namespace SubexponentialSAT.Subexp.UniversalRowGuard

open BitProgram StructuredCalls StackRoutines

abbrev count : Cmd 8 32 := .call (ProgramLinking.liftProgram
  SubexpSunflowerProgram.CountRecords.program countRegs countStacks)

abbrev compare : Cmd 8 32 := .call (ProgramLinking.liftProgram UnaryCompare.program compareRegs compareStacks)

abbrev compareClean : Cmd 8 32 :=
  .seq compare (.seq (.call (clearProgram 14 (0 : Fin 8) 1))
    (.call (clearProgram 11 (0 : Fin 8) 1)))

end SubexponentialSAT.Subexp.UniversalRowGuard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Word)
open UniversalRowFactorLoop (indexWord)

def ports : RecordPrograms.Ports 8 32 where
  tag := 5
  present := 6
  found := 7
  source := 17
  payload := 16
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchTypes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

open BitProgram StructuredCalls StackRoutines MulticolorTypes

abbrev clearRows : Cmd 10 49 :=
  .seq (.call (clearProgram 17 (0 : Fin 10) 1))
    (.seq (.call (clearProgram 18 (0 : Fin 10) 1))
      (.seq (.call (clearProgram 19 (0 : Fin 10) 1))
        (.call (clearProgram 20 (0 : Fin 10) 1))))

variable {r Q Δ : ℕ}

def extractBudget (i : Fin Δ) : ℕ :=
  36 * CollisionProgram.typeWidth r Q Δ +
    4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
end


