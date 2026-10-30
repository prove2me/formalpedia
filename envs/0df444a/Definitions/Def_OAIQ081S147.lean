-- Prove2me | Definitions.Def_OAIQ081S147
-- name    : OAIQ081S147
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:53:15.319358+00:00
-- url     : https://prove2.me/theorems/43d04584-62a5-4fd4-9c12-96100df27298
-- title:
--   Definitions bundle OAIQ081S147 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 32 definitions and 35 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.exportCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.exported`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.finishCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide.staged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint.outputStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.produced`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows.transferred`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.core`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.extent`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.parameters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingLoaderProgram.sizeBound`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.budget`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.command`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.extent`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.program`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.seedSize`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.sourceBudget`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputProgram.sourceCharge`, `OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram.sourceBudget`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_NativePackingBounds`, `SubexponentialSAT_SqrtLog_NativePackingBoundsTail`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsCore`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsLoader`, `SubexponentialSAT_SqrtLog_PackingCallerProgramExport`, `SubexponentialSAT_SqrtLog_PackingCallerProgramModel`, `SubexponentialSAT_SqrtLog_PackingCallerProgramReplay`, `SubexponentialSAT_SqrtLog_PackingCallerProgramStage`, `SubexponentialSAT_SqrtLog_PackingCallerProgramWide`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEndpoint`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingLoaderProgram`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramBounds`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramCore`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramParameters`, `SubexponentialSAT_Subexp_AssignmentInputProgram`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_CandidateScoreProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S116`, `OAIQ081S117`, `OAIQ081S123`, `OAIQ081S124`, `OAIQ081S130`, `OAIQ081S131`, `OAIQ081S132` and `OAIQ081S134` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S159`, `OAIQ081S160`, `OAIQ081S161`, `OAIQ081S162` and `OAIQ081S164`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S117
import Definitions.Def_OAIQ081S123
import Definitions.Def_OAIQ081S124
import Definitions.Def_OAIQ081S130
import Definitions.Def_OAIQ081S131
import Definitions.Def_OAIQ081S132
import Definitions.Def_OAIQ081S134

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control candidate scoring

Score records are accumulated as reversed serialized bytes and reversed once
at the end, so output score order agrees with the input candidate order.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def sourceBudget (ctx : Context) : ℕ :=
  7 * (ProgramEncoding.encodeRecords ctx.candidates).length +
    RecordPrograms.budget (callbackCost ctx) ctx.candidates +
    3 * (ProgramEncoding.encodeRecords (scoreRecords ctx)).length + 14

end SubexponentialSAT.Subexp.CandidateScoreProgram

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

theorem budget_le (n : ℕ) : budget n ≤ 60 * (n + 1) ^ 2 := by
  have hlength : (DimensionProgram.earlierRows 0 n).length = n := by
    simp [earlierRows_eq]
  have hwidth : ∀ bits ∈ DimensionProgram.earlierRows 0 n, bits.length ≤ n := by
    intro bits hb
    rw [earlierRows_eq] at hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' : i < n := by simpa using hi
    simp only [List.length_replicate]
    omega
  have hsize := ProgramEncoding.encodeRecords_length_le
    (DimensionProgram.earlierRows 0 n) n hwidth
  rw [hlength] at hsize
  unfold budget
  rw [DimensionProgram.loopCost_eq]
  nlinarith

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsTail
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Bounds for the actual packing tail

All sizes below come from the represented input and generated records.
There is no assumed runtime certificate: the cost estimates apply to the
same leftover and inverse budgets used by `PackingExecution.program_trace`.
-/

namespace SubexponentialSAT.SqrtLog.NativePackingBounds

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking LayoutProgram LayoutProgram.NativePacking

variable {U : Type*} [DecidableEq U]

/-- Every type occurs in the actual generated type stream. -/
theorem type_word_length_le (s : Spec U) (u : U) :
    (s.encodeType u).length ≤ s.params.typeStream.length := by
  change (s.encodeType u).length ≤ (ProgramEncoding.encodeRecords s.params.typeRows).length
  apply word_length_le_encoded
  rw [s.type_records]
  exact List.mem_map.mpr ⟨u, s.types.complete u, rfl⟩

theorem metadata_value_length_le (s : Spec U) (v : Fin s.suffix.params.D) :
    (PackingMetadata.value s.suffix.packing s.encodeType v).encode.length ≤
      2 * s.suffix.params.D + 2 * s.params.typeStream.length + 3 := by
  cases hl : s.suffix.packing.lookup v with
  | none =>
    have hi : s.suffix.packing.leftovers.idxOf v ≤ s.suffix.packing.leftovers.length := List.idxOf_le_length
    have hn := leftovers_length_le s
    simp only [PackingMetadata.value, hl, GlobalBasisMetadata.Metadata.encode,
      List.length_cons, Encoding.length_frame, PackingMetadata.unary, List.length_replicate]
    omega
  | some z =>
    have ht := type_word_length_le s z.2
    have hz := z.1.isLt
    have hb := (s.suffix.packing.blockCount_le_bucket z.2).trans (s.suffix.packing.bucket_length_le z.2)
    simp only [PackLabels.Spec.packing_vertices, List.length_finRange] at hb
    change s.suffix.packing.blockCount ≤ s.suffix.params.D at hb
    simp only [PackingMetadata.value, hl, GlobalBasisMetadata.Metadata.encode,
      List.length_cons, List.length_append, Encoding.length_frame,
      PackingMetadata.unary, List.length_replicate]
    omega

theorem metadata_list_length_le (s : Spec U) (vs : List (Fin s.suffix.params.D))
    (hn : vs.length ≤ s.suffix.params.D) :
    (SelectorProgram.rawRecords (vs.map (PackingMetadata.row s.suffix.packing s.suffix.encodeVertex s.encodeType))).length ≤
      metadataBound s.suffix.params.D s.params.typeStream.length := by
  have h := raw_length_le (vs.map (PackingMetadata.row s.suffix.packing s.suffix.encodeVertex s.encodeType))
    s.suffix.params.D (2 * s.suffix.params.D + 2 * s.params.typeStream.length + 3)
    (by
      intro row hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      simpa only [PackingMetadata.row, PackLabels.Spec.encodeVertex, List.length_replicate] using
        Nat.le_of_lt v.isLt)
    (by
      intro row hr
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
      exact metadata_value_length_le s v)
  simp only [List.length_map] at h
  calc
    _ ≤ vs.length * (2 * s.suffix.params.D + 2 *
      (2 * s.suffix.params.D + 2 * s.params.typeStream.length + 3) + 2) := h
    _ ≤ s.suffix.params.D * (2 * s.suffix.params.D + 2 *
      (2 * s.suffix.params.D + 2 * s.params.typeStream.length + 3) + 2) :=
      Nat.mul_le_mul_right _ hn
    _ = _ := by unfold metadataBound; ring

theorem covered_length_le (s : Spec U) :
    (SelectorProgram.rawRecords (PackLabels.covered s.suffix)).length ≤
      metadataBound s.suffix.params.D s.params.typeStream.length := by
  exact metadata_list_length_le s (PackingReorder.packedVertices s.suffix.packing).reverse
    (by simpa only [List.length_reverse] using packed_vertices_length_le s)

theorem metadata_length_le (s : Spec U) :
    s.suffix.metadata.length ≤ metadataBound s.suffix.params.D s.params.typeStream.length := by
  exact metadata_list_length_le s (PackingReorder.storageVertices s.suffix.packing).reverse
    (by simpa only [List.length_reverse] using storage_vertices_length_le s)

theorem storage_length_le (s : Spec U) : s.suffix.storage.length ≤ wordBound s.suffix.params.D :=
  encoded_vertices_length_le s (PackingReorder.storageVertices s.suffix.packing) (storage_vertices_length_le s)

theorem inverse_length_le (s : Spec U) : s.suffix.inverse.length ≤ wordBound s.suffix.params.D := by
  have h := ProgramEncoding.encodeRecords_length_le
    ((PackingReorder.readPlan s.suffix.packing).map PackingMetadata.unary) s.suffix.params.D (by
      intro word hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hi
      simpa only [PackingMetadata.unary, List.length_replicate] using
        (List.idxOf_le_length (a := v) (l := PackingReorder.storageVertices s.suffix.packing)).trans
          (storage_vertices_length_le s))
  simpa only [PackLabels.Spec.inverse, List.length_map, PackingReorder.readPlan_length,
    PackLabels.Spec.packing_vertices, List.length_finRange, wordBound] using h

/-- The initial leftover state is obtained from the proved extraction output. -/
theorem context_snapshot (s : Spec U) :
    PackingOutputSemantics.snapshotOf (PackLabels.context s.suffix) =
      PackingOutputSemantics.packedSnapshot s.suffix.packing Fin.val s.encodeType := by
  exact PackingOutputSemantics.snapshotOf_extraction s.suffix.packing Fin.val s.encodeType
    (PackingProgram.initialExtraction (PackLabels.entries s.suffix) s.suffix.packing.blockCount) rfl rfl rfl rfl rfl

theorem context_address_length_le (s : Spec U) : (PackLabels.context s.suffix).address.length ≤ s.params.D := by
  have h := congrArg PackingLeftovers.Snapshot.address (context_snapshot s)
  change (PackLabels.context s.suffix).address.length = (PackingReorder.packedVertices s.suffix.packing).length at h
  rw [h]
  exact packed_vertices_length_le s

theorem inverse_budget_le (s : Spec U) :
    PackingProgram.inverseBudget (PackLabels.addressRecords s.suffix) s.params.D ≤ inversePolynomial s.params.D := by
  have ha := address_records_length_le s
  rw [suffix_D] at ha
  have hq := queries_length_le s.params.D
  have hi : (ProgramEncoding.encodeRecords
      (PackingProgram.inverseRows (PackLabels.addressRecords s.suffix) s.params.D)).length ≤ wordBound s.params.D := by
    have hir := PackLabels.inverse_rows s.suffix
    change PackingProgram.inverseRows (PackLabels.addressRecords s.suffix) s.params.D = _ at hir
    rw [hir]
    exact inverse_length_le s
  have hsel : SelectorMapProgram.budget (PackLabels.addressRecords s.suffix) (PackingProgram.inverseQueries s.params.D) ≤
      500 * (addressBound s.params.D + 1) * (wordBound s.params.D + 1) := by
    calc
      _ ≤ 500 * ((SelectorProgram.rawRecords (PackLabels.addressRecords s.suffix)).length + 1) *
        ((ProgramEncoding.encodeRecords (PackingProgram.inverseQueries s.params.D)).length + 1) :=
          SelectorMapProgram.budget_bound _ _
      _ ≤ _ := by gcongr
  unfold PackingProgram.inverseBudget inversePolynomial
  omega

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial cost of the actual native address-plan suffix. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram LayoutProgram
variable {U : Type*} [DecidableEq U]

theorem input_types (s : NativePacking.Spec U) :
    s.params.typeStream=ProgramEncoding.encodeRecords (PackLabels.keys s.suffix) := by
  rw [NativeFrontend.Params.typeStream,s.type_records]
  rfl

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def data (r : Fin 6 → Bool) (h n : ℕ) (source out payload : List Bool)
    (factor : List Bool := []) : Data :=
  ⟨r, ![unary h,unary n,payload,factor,[],[],[],out,source]⟩
def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks 1 3 d.stacks⟩
def transferred (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 2 3 d.stacks⟩
def cleared (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 3 []⟩

theorem state_data (r : Fin 6 → Bool) (h n : ℕ)
    (source out payload : List Bool) (t pr f : Bool) (src pay : List Bool) :
    RecordPrograms.state readerPorts (data r h n source out payload) t pr f src pay =
      data (Function.update (Function.update (Function.update r 3 t) 4 pr) 5 f)
        h n src out pay := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i; fin_cases i <;> simp [readerPorts,data]

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Rows


/-! Native per-variable incident-factor scan from the original scope stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def data (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) : Data :=
  ⟨r, fun j => if j=20 then scopeBits scopes else if j=21 then unary n
    else if j=22 then unary v else if j=24 then unary z else if j=25 then out
    else if j=26 then mask else []⟩
def result (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) : Data :=
  ⟨r, fun j => if j=2 then (Encoding.encodeNat v).reverse
    else if j=5 then unary scopes.length
    else if j=7 then Encoding.encodeList unary (indices scopes v).reverse
    else if j=9 then unary (indices scopes v).length
    else (data r scopes n v z mask out).stacks j⟩

def copied (src dst : Fin 32) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩
theorem copy_eval (src dst : Fin 32) (hsd : src ≠ dst) (hs : src ≠ 31)
    (hd : (31 : Fin 32) ≠ dst) (d : Data) (ht : d.stacks 31 = []) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  TupleProgram.copy_eval src dst 31 0 1 hsd hs hd (by decide) d ht

def prepared (d : Data) : Data := TupleProgram.pushedState 7 0 false
  (TupleProgram.pushedState 2 0 false (copied 22 2 (copied 20 6 d)))

theorem prepare_eval (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n v z : ℕ)
    (mask out : List Bool) :
    Eval prepare (7*((scopeBits scopes).length+v)+14) (data r scopes n v z mask out)
      (prepared (data r scopes n v z mask out)) := by
  let a := data r scopes n v z mask out
  let b := copied 20 6 a
  let c := copied 22 2 b
  let d := TupleProgram.pushedState 2 0 false c
  have h1 := copy_eval 20 6 (by decide) (by decide) (by decide) a (by simp [a,data])
  have h2 := copy_eval 22 2 (by decide) (by decide) (by decide) b
    (by simp [b,copied,a,data,StackRoutines.copyStacks])
  have h3 := TupleProgram.pushConst_eval (2 : Fin 32) (0 : Fin 16) false c
  have h4 := TupleProgram.pushConst_eval (7 : Fin 32) (0 : Fin 16) false d
  have hh := h1.seq (h2.seq (h3.seq h4))
  convert hh using 1 <;>
    simp [prepared, a, b, c, d, copied, data, StackRoutines.copyStacks,
      Nat.mul_add, Nat.add_assoc]
  omega

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Scan


/-! Fixed cleanup for the native scope-address scanner. -/


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev command : Cmd 16 32 := .seq (Scan.copy 20 0)
  (.seq count (TupleProgram.pushConst 25 0 false))
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputInstall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw scope bytes and a mask produce the actual installed incidence-pair table. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
noncomputable def state (d : Scan.Data) : Data := embedState id ports (frame d.regs) d
noncomputable def input (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  state (Scan.data r scopes n 0 0 mask [])
noncomputable def produced (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :=
  state (Scan.data r scopes n mask.length (Loop.finalCounter scopes 0 scopes.length mask) []
    (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet
      (Loop.plans scopes n 0 scopes.length mask))))

theorem state_register (d : Scan.Data) (i : Fin 16) : (state d).regs i = d.regs i :=
  embedState_register id ports (frame d.regs) d Function.injective_id i
theorem state_stack (d : Scan.Data) (i : Fin 32) : (state d).stacks (ports i) = d.stacks i :=
  embedState_stack id ports (frame d.regs) d ports_injective i
theorem state_frame (d : Scan.Data) (j : Fin 48) (hj : ¬ ∃ i, ports i=j) :
    (state d).stacks j = [] :=
  embedState_stack_frame id ports (frame d.regs) d j hj

theorem depth_eval (d : Data) : Eval depth 4 d (withDepth d) :=
  (TupleProgram.pushConst_eval (27 : Fin 48) (0 : Fin 16) true d).seq
    (TupleProgram.pushConst_eval (27 : Fin 48) (0 : Fin 16) true
      (TupleProgram.pushedState 27 0 true d))

theorem installed_input (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    PackingIncidenceProgram.Install.Input (plans scopes n mask)
      (withDepth (produced r scopes n mask)) := by
  let d := Scan.data r scopes n mask.length (Loop.finalCounter scopes 0 scopes.length mask) []
    (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet (plans scopes n mask)))
  have hs (j : Fin 32) : (produced r scopes n mask).stacks (ports j) = d.stacks j :=
    state_stack d j
  have h21 : (produced r scopes n mask).stacks 21 = [] := state_frame d 21 (by decide)
  have h22 : (produced r scopes n mask).stacks 22 = [] := state_frame d 22 (by decide)
  have h24 : (produced r scopes n mask).stacks 24 = [] := state_frame d 24 (by decide)
  have h25 : (produced r scopes n mask).stacks 25 = [] := state_frame d 25 (by decide)
  have h26 : (produced r scopes n mask).stacks 26 = [] := state_frame d 26 (by decide)
  have h45 : (produced r scopes n mask).stacks 45 = [] := state_frame d 45 (by decide)
  have h0 := hs 0
  have h7 := hs 7
  have h20 := hs 25
  have h23 := hs 23
  have h27 := hs 27
  simp [ports] at h0 h7 h20 h23 h27
  constructor
  · intro i
    fin_cases i <;> simp [PackingIncidenceProgram.Install.ports,withDepth,
      TupleProgram.pushedState,PackingIncidenceProgram.pairInput,
      h0,h20,h21,h22,h23,h24,h25,h26,h27,d,Scan.data]
  · constructor <;> simp [withDepth,TupleProgram.pushedState,h7,h45,d,Scan.data]

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Install

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Entry from the actual descending high mask produced by the high-variable pass. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Entry
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem install_stacks (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Install.input r scopes n mask).stacks = sourceStacks scopes n mask := by
  let d := Scan.data r scopes n 0 0 mask []
  funext j
  by_cases hj : ∃ i, Install.ports i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [show (Install.input r scopes n mask).stacks (Install.ports i) = d.stacks i from
      Install.state_stack d i]
    fin_cases i <;> simp [d,Scan.data,Install.ports,sourceStacks]
  · rw [show (Install.input r scopes n mask).stacks j = [] from Install.state_frame d j hj]
    have h32 : j ≠ 32 := fun h => hj ⟨20,h.symm⟩
    have h33 : j ≠ 33 := fun h => hj ⟨21,h.symm⟩
    have h36 : j ≠ 36 := fun h => hj ⟨26,h.symm⟩
    simp [sourceStacks,h32,h33,h36]
theorem install_eq (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    Install.input r scopes n mask = ⟨r,sourceStacks scopes n mask⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    exact Install.state_register (Scan.data r scopes n 0 0 mask []) i
  · exact install_stacks r scopes n mask

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Entry


/-! Raw scopes and the computed mask feed the actual incidence-pair producer. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputEndpoint
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact five-port handoff from the native incidence producer to its loader. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def outputStacks (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Fin 48 → List Bool :=
  fun j => if j=32 then Scan.scopeBits scopes else if j=33 then Scan.unary n
    else if j=34 then Scan.unary mask.length
    else if j=35 then Scan.unary (Semantics.factorCount scopes mask)
    else if j=45 then PairScoreProgram.pairRecords
      (PackingIncidenceProgram.generatedRawPairs (Install.plans scopes n mask)) else []

def result (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) : Data :=
  ⟨r,outputStacks scopes n mask⟩

theorem produced_stacks (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Install.produced r scopes n mask).stacks = builtStacks scopes n mask := by
  let d := Scan.data r scopes n mask.length (Semantics.factorCount scopes mask) []
    (ProgramEncoding.encodeRecords (PackingIncidenceProgram.planAlphabet (Install.plans scopes n mask)))
  funext j
  by_cases hj : ∃ i, Install.ports i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [show (Install.produced r scopes n mask).stacks (Install.ports i) = d.stacks i from
      Install.state_stack d i]
    fin_cases i <;> simp [d,Scan.data,Install.ports,builtStacks]
  · rw [show (Install.produced r scopes n mask).stacks j = [] from
      Install.state_frame d j hj]
    have h32 : j ≠ 32 := fun h => hj ⟨20,h.symm⟩
    have h33 : j ≠ 33 := fun h => hj ⟨21,h.symm⟩
    have h34 : j ≠ 34 := fun h => hj ⟨22,h.symm⟩
    have h35 : j ≠ 35 := fun h => hj ⟨24,h.symm⟩
    have h20 : j ≠ 20 := fun h => hj ⟨25,h.symm⟩
    simp [builtStacks,h32,h33,h34,h35,h20]

theorem exact_output (r : Fin 16 → Bool) (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (e : Data)
    (hout : e.stacks 45 = PairScoreProgram.pairRecords
      (PackingIncidenceProgram.generatedRawPairs (Install.plans scopes n mask)))
    (hz : ∀ j, j=0 ∨ j=7 ∨ j ∈ PackingIncidenceProgram.Install.bank → e.stacks j = [])
    (hf : ∀ j, j≠0 → j≠7 → j≠45 → j ∉ PackingIncidenceProgram.Install.bank →
      e.stacks j = (Install.withDepth (Install.produced r scopes n mask)).stacks j) :
    e = result e.regs scopes n mask := by
  apply congrArg (StructuredProgram.State.mk e.regs)
  funext j
  by_cases hc : j=0 ∨ j=7 ∨ j ∈ PackingIncidenceProgram.Install.bank
  · rw [hz j hc]
    have h32 : j ≠ 32 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    have h33 : j ≠ 33 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    have h34 : j ≠ 34 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    have h35 : j ≠ 35 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    have h45 : j ≠ 45 := by intro h; subst j; simp [PackingIncidenceProgram.Install.bank] at hc
    simp only [outputStacks, ite_eq_right h32, ite_eq_right h33, ite_eq_right h34, ite_eq_right h35, ite_eq_right h45]
  · have h0 : j ≠ 0 := fun h => hc (Or.inl h)
    have h7 : j ≠ 7 := fun h => hc (Or.inr (Or.inl h))
    have hb : j ∉ PackingIncidenceProgram.Install.bank := fun h => hc (Or.inr (Or.inr h))
    by_cases h45 : j=45
    · subst j; simpa [outputStacks] using hout
    · have h20 : j ≠ 20 := by intro h; subst j; exact hb (by decide)
      have h27 : j ≠ 27 := by intro h; subst j; exact hb (by decide)
      rw [hf j h0 h7 h45 hb]
      simp [Install.withDepth,TupleProgram.pushedState,produced_stacks,
        builtStacks,outputStacks,h20,h27,h45]

end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Endpoint

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

def seedSize : Code := .seq seedProduct (copyCmd 5 47 31)

def command : Code :=
  .seq colorAlphabet (.seq wordAlphabet (.seq firstWord (.seq packedAlphabet
    (.seq wordWidth (.seq deltaPlusOne (.seq depth (.seq seedSize (.seq seedRange cleanup))))))))

abbrev program : Program 16 48 (size command + 1) := compiled command 1 30

def sourceCharge (r Q delta D E : ℕ) : ℕ :=
  let rows := AssignmentAlphabetSemantics.wordBytes r Q
  (60 * (r + 1) ^ 2 + 1) +
  (TupleProgram.powerCost (OneHotAlphabetProgram.rows 0 r) Q [[]] + 9) +
  (9 * (rows.headD []).length + 10) +
  (9 * (rows.map List.length).sum + 6 * rows.length + 7) +
  (Q * (7 * r + 7) + 3) + (7 * delta + 7) +
  (14 * (delta + 1) + 10) +
  ((delta + 1) * (7 * D + 7) + 3 + (7 * E + 5)) +
  (AssignmentSeedRange.budget (seedCount delta D E) + 1)

def sourceBudget (r Q delta D E B : ℕ) : ℕ :=
  sourceCharge r Q delta D E + 5000 * (B + 1)

/-- Explicit data-size envelope, including generated arrays. It is assertion
notation only; no bound or table is passed to the machine. -/
def extent (r Q delta D E : ℕ) (pairs : List Bool) : ℕ :=
  let rows := AssignmentAlphabetSemantics.wordBytes r Q
  1 + r + Q + delta + D + E + (delta + 1) + 2 * (delta + 1) + Q * r +
    seedCount delta D E + r ^ Q +
    (ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r)).length +
    (ProgramEncoding.encodeRecords rows).length + (rows.headD []).length + rows.flatten.length +
    (AssignmentSeedRange.seedRecords (seedCount delta D E)).length + pairs.length

def budget (r Q delta D E : ℕ) (pairs : List Bool) : ℕ :=
  sourceBudget r Q delta D E (extent r Q delta D E pairs)

theorem extent_le_sizeBound (r Q delta D E : ℕ) (pairs : List Bool) (hr : 0 < r) :
    extent r Q delta D E pairs ≤ sizeBound r Q delta D E pairs.length := by
  have hc : ∀ bits ∈ OneHotAlphabetProgram.rows 0 r, bits.length ≤ r := by
    intro bits hb
    rw [AssignmentAlphabetSemantics.rows_eq_alphabet] at hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    simp [AssignmentAlphabetSemantics.oneHot]
  have hclen : (OneHotAlphabetProgram.rows 0 r).length = r := by
    simp [AssignmentAlphabetSemantics.rows_eq_alphabet]
  have hcolor := ProgramEncoding.encodeRecords_length_le (OneHotAlphabetProgram.rows 0 r) r hc
  rw [hclen] at hcolor
  have hw : ∀ bits ∈ AssignmentAlphabetSemantics.wordBytes r Q, bits.length ≤ Q * r :=
    fun bits hb => (AssignmentAlphabetSemantics.wordBytes_width hr bits hb).le
  have hwords := ProgramEncoding.encodeRecords_length_le
    (AssignmentAlphabetSemantics.wordBytes r Q) (Q * r) hw
  rw [AssignmentAlphabetSemantics.wordBytes_length] at hwords
  have hvolume := PairScoreBounds.volume_le (AssignmentAlphabetSemantics.wordBytes r Q) (Q * r) hw
  rw [AssignmentAlphabetSemantics.wordBytes_length] at hvolume
  have hflat : (AssignmentAlphabetSemantics.wordBytes r Q).flatten.length ≤ r ^ Q * (Q * r) := by
    simpa only [List.length_flatten, PairScoreBounds.volume] using hvolume
  have hhead : ((AssignmentAlphabetSemantics.wordBytes r Q).headD []).length = Q * r := by
    obtain ⟨a, tail, he, _, _⟩ := AssignmentAlphabetSemantics.wordBytes_order hr Q
    rw [← he]
    simp [ReadPlan.encodeWord_length, ReadPlan.wordWidth]
  have hseeds := ProgramEncoding.encodeRecords_length_le
    ((List.range (seedCount delta D E)).map unary) (seedCount delta D E) (by
      intro bits hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      simpa using (List.mem_range.mp hi).le)
  simp only [List.length_map, List.length_range] at hseeds
  change (AssignmentSeedRange.seedRecords (seedCount delta D E)).length ≤ _ at hseeds
  dsimp only [extent, sizeBound]
  rw [hhead]
  omega

theorem budget_le (r Q delta D E : ℕ) (pairs : List Bool) (hr : 0 < r) :
    budget r Q delta D E pairs ≤ 20000 * (extent r Q delta D E pairs + 1) ^ 4 := by
  let B := extent r Q delta D E pairs
  let T := B + 1
  have hrB : r ≤ B := by dsimp [B, extent]; omega
  have hQB : Q ≤ B := by dsimp [B, extent]; omega
  have hdB : delta ≤ B := by dsimp [B, extent]; omega
  have hd1B : delta + 1 ≤ B := by dsimp [B, extent]; omega
  have hDB : D ≤ B := by dsimp [B, extent]; omega
  have hEB : E ≤ B := by dsimp [B, extent]; omega
  have hMB : seedCount delta D E ≤ B := by dsimp [B, extent]; omega
  have hpowB : r ^ Q ≤ B := by dsimp [B, extent]; omega
  have hhead : ((AssignmentAlphabetSemantics.wordBytes r Q).headD []).length ≤ B := by
    dsimp [B, extent]; omega
  have hflat : ((AssignmentAlphabetSemantics.wordBytes r Q).map List.length).sum ≤ B := by
    have h : (AssignmentAlphabetSemantics.wordBytes r Q).flatten.length ≤ B := by
      dsimp [B, extent]; omega
    simpa only [List.length_flatten] using h
  have hcount : (AssignmentAlphabetSemantics.wordBytes r Q).length ≤ B := by
    simpa using hpowB
  have hcolorlen : (OneHotAlphabetProgram.rows 0 r).length = r := by
    rw [AssignmentAlphabetSemantics.rows_eq_alphabet]
    simp
  have hcolorwidth : ∀ bits ∈ OneHotAlphabetProgram.rows 0 r, bits.length ≤ r := by
    intro bits hb
    rw [AssignmentAlphabetSemantics.rows_eq_alphabet] at hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    simp [AssignmentAlphabetSemantics.oneHot]
  have hpower := PairScoreBounds.generated_powerCost_le (OneHotAlphabetProgram.rows 0 r) Q r
    (by rw [hcolorlen]; omega) hcolorwidth
  rw [hcolorlen] at hpower
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hrT : r + 1 ≤ T := by dsimp [T]; omega
  have hQT : Q + 1 ≤ T := by dsimp [T]; omega
  have hDT : D + 1 ≤ T := by dsimp [T]; omega
  have hMT : seedCount delta D E + 1 ≤ T := by dsimp [T]; omega
  have hlast : (Q + 1) * r + 1 ≤ T ^ 2 := by
    have hh := Nat.mul_le_mul hQT hrB
    dsimp [T] at hh ⊢
    nlinarith only [hh]
  have hpower' : TupleProgram.powerCost (OneHotAlphabetProgram.rows 0 r) Q [[]] ≤ 800 * T ^ 4 := by
    calc
      _ ≤ 800 * T * T * T ^ 2 := hpower.trans (by gcongr ; omega)
      _ = _ := by ring
  have hcolor : 60 * (r + 1) ^ 2 ≤ 60 * T ^ 2 := by gcongr
  have hseed : AssignmentSeedRange.budget (seedCount delta D E) ≤ 60 * T ^ 2 :=
    (AssignmentSeedRange.budget_le _).trans (by gcongr)
  have hwidth : Q * (7 * r + 7) ≤ 7 * T ^ 2 := by
    calc
      _ = 7 * Q * (r + 1) := by ring
      _ ≤ 7 * T * T := by gcongr ; omega
      _ = _ := by ring
  have hproduct : (delta + 1) * (7 * D + 7) ≤ 7 * T ^ 2 := by
    calc
      _ = 7 * (delta + 1) * (D + 1) := by ring
      _ ≤ 7 * T * T := by gcongr ; omega
      _ = _ := by ring
  have hT2 : T ≤ T ^ 2 := le_self_pow hT (by decide)
  have hT4 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right' hT (by decide)
  have hcharge : sourceCharge r Q delta D E ≤
      800 * T ^ 4 + 134 * T ^ 2 + 52 * B + 56 := by
    dsimp only [sourceCharge]
    omega
  have hBT : B + 1 = T := rfl
  change sourceCharge r Q delta D E + 5000 * T ≤ 20000 * T ^ 4
  omega

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native alphabet/seed construction followed by actual assignment copying.
The old producer is used at delta=0 so the seed count is exactly ambient+factors;
the new scorer's four-word depth is installed separately. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def core : Code :=
  .seq (.call (ProgramLinking.liftProgram AssignmentInputProgram.program id lowPorts))
    (.call (ProgramLinking.liftProgram AssignmentInitProgram.program id lowPorts))

def extent (r Q n f : ℕ) (pairs : List Bool) :=
  AssignmentInputProgram.extent r Q 0 n f pairs

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid conversion of the actual binary radius and coordinate parameters. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def parameters : Code := .seq (unaryCommand radiusPorts) (unaryCommand coordinatePorts)

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native loader from the incidence installer's actual tapes and
binary metadata to the sequential packing selector's initialized tapes. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def command : Code := .seq capture (.seq parameters (.seq core finish))

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The loader's complete native cost, including emitted alphabet size. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def sizeBound (outside : Store) (scopes : List Bool) (n k f : ℕ) (pairs : List Bool) : ℕ :=
  extent (SubexponentialSAT.BinaryArithmetic.toNat (outside 59))
    (SubexponentialSAT.BinaryArithmetic.toNat (outside 55)) n f pairs + scopes.length+n+k+f+
  SubexponentialSAT.BinaryArithmetic.toNat (outside 59)+SubexponentialSAT.BinaryArithmetic.toNat (outside 55)+
  (outside 55).length+(outside 56).length+(outside 57).length+(outside 58).length+
  (outside 59).length+1

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

namespace Problem

theorem spec_plans (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (p.spec a tail).params.planStream=planBits p.scopes p.n p.mask :=
  Address.planBytes_eq p.scopes p.n p.mask p.mask_le (p.words a tail) (p.words_length a tail)

end Problem

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

theorem plans_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (planBits p.scopes p.n p.mask).length ≤ planEnvelope S := by
  have hp := NativePackingBounds.address_plan_stream_le (p.words a tail)
    (Address.address p.scopes p.n p.mask p.mask_le (p.words a tail) (p.words_length a tail))
  change (p.spec a tail).params.planStream.length ≤ _ at hp
  rw [p.spec_plans,p.words_length] at hp
  apply hp.trans
  unfold planEnvelope
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  calc
    _ ≤ 1+(16*(2*S)+24)*S := by gcongr; exact h.incidences
    _ = _ := by ring

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem extent_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S) :
    extent p.r p.Q p.n p.factors (PairScoreProgram.pairRecords p.raw) ≤ extentEnvelope S := by
  apply (AssignmentInputProgram.extent_le_sizeBound p.r p.Q 0 p.n p.factors
    (PairScoreProgram.pairRecords p.raw) p.hr).trans
  unfold AssignmentInputProgram.sizeBound AssignmentInputProgram.seedCount extentEnvelope
    alphabetEnvelope seedEnvelope
  simp only [zero_add,one_mul]
  have hn : p.factors+p.n ≤ 2*S := by have := h.n; have := h.factors; omega
  have hw := width_le h
  have hb := pair_bytes_le h
  gcongr <;> first | exact h.r | exact h.Q | exact h.n | exact h.factors | exact hn | exact hw | exact h.alphabet

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBoundsCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem produce_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    produceBudget p.scopes p.n p.mask ≤ produceEnvelope S := by
  have hb := Cost.native_cubic p.scopes p.n p.mask
  have hp := plans_le h a tail
  have hi := Finished.pair_budget_le p.scopes p.n p.mask p.mask_le
  change _ ≤ 100*(2400*(p.incidences+1)^2*(24*(p.n+p.factors)+34)+11+
    (16*(p.n+p.factors)+24)*p.incidences) at hi
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have hinput : Cost.inputSize p.scopes p.n p.mask ≤ 3*S+1 := by
    have := h.scopes; have := h.n; have := h.mask
    dsimp [Cost.inputSize]; omega
  unfold produceBudget produceEnvelope
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.add_le_add_right (hb.trans (by gcongr)) 1
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left 7 hp) 5
  · apply Nat.add_le_add_left
    exact hi.trans (by gcongr <;> exact h.incidences)

theorem prepare_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (hp : Parameters outside p) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    prepareBudget (selectedStore outside p a tail) ≤ prepareEnvelope S := by
  have hplan := plans_le h a tail
  have ha := alphabet_bytes_le h
  have hw := width_le h
  have hn : p.n+p.factors ≤ 2*S := by have := h.n; have := h.factors; omega
  have h58 : selectedStore outside p a tail 58=outside 58 := by
    simp [selectedStore,cached,loadedStore,planStore]
  have h61 : selectedStore outside p a tail 61=planBits p.scopes p.n p.mask := by
    simp [selectedStore,cached,loadedStore,planStore]
  have h62 : selectedStore outside p a tail 62=((p.words a tail).map ReadPlan.encodeWord).flatten := by
    simp [selectedStore]
  have h53 : selectedStore outside p a tail 53=List.replicate (p.Q*p.r) true := by
    simp [selectedStore,cached]
  have h54 : selectedStore outside p a tail 54=ProgramEncoding.encodeRecords
      (AssignmentAlphabetSemantics.wordBytes p.r p.Q) := by
    simp [selectedStore,cached]
  unfold prepareBudget
  rw [h58,h61,h62,h53,h54,LeafParametersProgram.Serialization.unaryCopyBound_eq,
    hp.incidence,words_bits,List.length_replicate]
  unfold prepareEnvelope
  gcongr <;> first | exact h.incidences | exact h.l58 | decide

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The caller's private64-stack workspace lies after the live native
parameter bank340..416, which must survive until ring setup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem bankCall_eval {L t : ℕ} (p : Program 16 64 L) (a : Data)
    (b : State 16 64)
    (h : Trace p t ((projectState registers ports a).withPC (some p.entry)) (b.withPC none)) :
    Eval (bankCall p) t a (embedState registers ports a b) :=
  eval_call_from_state p registers ports a registers.injective ports.injective h

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramExport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid export of the computed word table, metadata, and original plans,
followed by erasure of the private bank and parking of the source masters. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

def exported (a : Local) : Local := clearManyState privatePorts (copyManyState exportPairs a)
def exportCost (a : Local) := copyManyCost exportPairs a+
  clearManyCost privatePorts (copyManyState exportPairs a)

def finished (a : Local) : Local := LeafProgram.LayoutMasters.parked (exported a)
def finishCost (a : Local) := exportCost a+LeafProgram.LayoutMasters.parkCost (exported a)

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid copies from the actual query frontend's persistent master bank. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

def staged (a : Local) : Local := copyManyState stagePairs a

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native packing caller neither reads nor writes the outer carried
tapes. Their contents therefore do not affect its exact running time. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
open LeafProgram.OuterCarried
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem wideCall_avoids (c : Cmd 16 768) (hc : AvoidsCmd LeafProgram.OuterCarried.hidden c) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Wide.call c) :=
  avoids_liftProgram LeafProgram.OuterCarried.hidden _ _ _ (avoids_compiled LeafProgram.OuterCarried.hidden c hc 684 133)

theorem stage_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Wide.stage := by
  apply wideCall_avoids
  apply avoids_copyMany LeafProgram.OuterCarried.hidden 684 Wide.stagePairs (away _ (by norm_num))
  intro p hp
  simp only [Wide.stagePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl  <;>
    exact ⟨away _ (by norm_num),bank_away _⟩

theorem export_avoids : AvoidsCmd LeafProgram.OuterCarried.hidden Wide.exportLocal := by
  constructor
  · apply avoids_copyMany LeafProgram.OuterCarried.hidden 684 Wide.exportPairs (away _ (by norm_num))
    intro p hp
    simp only [Wide.exportPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl  <;>  exact ⟨bank_away _,away _ (by norm_num)⟩
  · apply avoids_clearMany
    intro p hp
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
    exact bank_away i

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Replay

end OAI.Algorithms
end


