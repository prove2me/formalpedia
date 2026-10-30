-- Prove2me | Definitions.Def_OAIQ081S168
-- name    : OAIQ081S168
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:10:43.542135+00:00
-- url     : https://prove2.me/theorems/5adb4250-019b-4453-9e3a-da0d76eefaf5
-- title:
--   Definitions bundle OAIQ081S168 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 30 definitions, 1 inductive type or structure and 7 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.LiteralReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.WorkReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.branchState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.clearedStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareIndices`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.deltaWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emitterSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.emitterStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.metadataStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.uncovered`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universalBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.vectorState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.packedSourceValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.totalPackedSource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.columnTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs.entryTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.bootCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.bootState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.cacheState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.initializeCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.nodeStart`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cacheLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.packingProblem`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.queryHeight`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_InterpolationCacheProgramLengths`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQuery`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBank`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankCost`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrame`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCalls`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCore`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameEmitter`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameFinish`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBankState`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceDispatch`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramNative`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramNativeCost`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceMeaning`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramInitialize`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeCache`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs`, `SubexponentialSAT_SqrtLog_LeafPackingFiberBoundsQuery`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExports`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramQueryPackingInput`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCore`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendNumericRun`, `SubexponentialSAT_SqrtLog_ProducedQueryRankMagnitude`, `SubexponentialSAT_Subexp_PackingLeftoverStage`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S153`, `OAIQ081S155`, `OAIQ081S156`, `OAIQ081S157` and `OAIQ081S158` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S173`, `OAIQ081S174`, `OAIQ081S175`, `OAIQ081S176`, `OAIQ081S177`, `OAIQ081S178` and `OAIQ081S179`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.shifted_source_typed`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_scalar_input_cap_of_scope_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.query_max_bound_rat`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.literal_cleanup_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_mismatch_branch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.uncovered_cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universalBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start_cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start_size`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.initializeCost_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBounds.query_factor_fiber_le` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.shifted_source_typed`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.scanner_caps_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_mismatch_branch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universalBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.nativeRowsBudget_le_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start_cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.start_size`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.initializeCost_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafPackingFiberBounds.query_factor_fiber_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_length` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage_eval_bounded`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S155
import Definitions.Def_OAIQ081S156
import Definitions.Def_OAIQ081S157
import Definitions.Def_OAIQ081S158

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramLengths
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact physical output lengths for relocation and cleanup costs. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT SubexpLiftRing

@[simp] theorem rowBytes_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) (x : Coeff t d) :
    (rowBytes t a M cache minusOne xs x).length=xs.length*(d*baseWidth 3 t) :=
  flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs

@[simp] theorem differenceBytes_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :
    (differenceBytes t a M cache minusOne xs).length=xs.length*(xs.length*(d*baseWidth 3 t)) :=
  flatMap_length _ _ (rowBytes_length t a M cache minusOne xs) xs

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem guard_preserves_public (m : Model) (i : Fin 12) :
    (result GuardSetup.code m).val (publicSlot i)=m.val (publicSlot i) := by
  rw [GuardSetup.code, result_append]
  have he : ∀ j ∈ GuardSetup.emissions, output j ≠ publicSlot i := by
    fin_cases i <;> decide
  have hp : ∀ j ∈ GuardSetup.preparation, output j ≠ publicSlot i := by
    fin_cases i <;> decide
  calc
    (result GuardSetup.emissions (result GuardSetup.preparation m)).val (publicSlot i) =
        (result GuardSetup.preparation m).val (publicSlot i) := by
      exact result_value_frame _ _ _ he
    _ = m.val (publicSlot i) := by
      exact result_value_frame _ _ _ hp

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramSerialization -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A denominator constructor consuming the actual ring-setup certificate.
The inverse-half fact comes from that executed setup, and the power is then
computed by the fixed native multiplication loop in the private bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexpLiftRing SubexpQuarticRing IntegerRingLiftProgram

theorem ready_of_caches (a : LocalData) (t d : ℕ) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) (e : LeafRingSetupProgram.Data)
    (h : LeafRingSetupProgram.RingCaches t d model M cache u e)
    (hf : ∀i : Fin 640,i.val < 340 → a.stacks (LeafRingSetupProgram.wideStacks i)=e.stacks i) :
    CachedReady t model M cache
      (LeafProgram.Constants.constantCode d cache.zero cache.zero)
      (LeafProgram.Constants.constantCode d cache.one cache.zero)
      (LeafProgram.Constants.constantCode d cache.minusOne cache.zero) (localInput a) := by
  have h194 := (hf 194 (by decide)).trans h.modulus
  have h201 := (hf 201 (by decide)).trans h.table
  have h202 := congrArg List.length (hf 202 (by decide))
  have h203 := (hf 203 (by decide)).trans h.scalarZero
  have h204 := congrArg List.length (hf 204 (by decide))
  have h280 := (hf 280 (by decide)).trans h.fullZero
  have h207 := (hf 207 (by decide)).trans h.fullOne
  have h211 := (hf 211 (by decide)).trans h.fullMinusOne
  refine ⟨?_,by simp [Clean,localInput],?_,?_,?_,by simp [localInput],by simp [localInput],
    by simp [localInput],by simp [localInput]⟩
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · refine ⟨by simp [localInput],?_⟩
      intro i
      fin_cases i <;> simp [ReconstructionProgram.RingAdapter.ports,
        ReconstructionProgram.RingAdapter.finalNative,ReconstructionProgram.RingAdapter.nativeStacks,localInput]
    · simpa [localInput,LeafRingSetupProgram.wideStacks] using h194
    · simpa [localInput,LeafRingSetupProgram.wideStacks] using h202.trans h.width
    · simpa [localInput,LeafRingSetupProgram.wideStacks] using h203
    · simpa [localInput,LeafRingSetupProgram.wideStacks,
        RingProgramTable.modelTable,IntegerRingLiftProgram.modelTable] using h201
    · simpa [localInput,LeafRingSetupProgram.wideStacks] using h204.trans h.degree
  · simpa [localInput,LeafRingSetupProgram.wideStacks,
      LeafProgram.Constants.constantCode_flat] using h280
  · simpa [localInput,LeafRingSetupProgram.wideStacks,
      LeafProgram.Constants.constantCode_flat] using h207
  · simpa [localInput,LeafRingSetupProgram.wideStacks,
      LeafProgram.Constants.constantCode_flat] using h211

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual generation of ascending vertex indices and the leftover scan in
the fixed packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

theorem vertices_eval (input : Input) (n D : ℕ) (c : PackingExtraction.Context)
    (hD : input.dimension = List.replicate D true) (regs : Fin 16 → Bool) :
    ∃ steps ≤ verticesBudget D, ∃ rf,
      Eval vertices steps (extractionOutputState input n c regs)
        (verticesOutputState input n D c rf) := by
  let a := extractionOutputState input n c regs
  have hv : PackingPlumbing.Valid verticesSetup a := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, verticesSetup,
      a, extractionOutputState, inputState]
  let b := PackingPlumbing.run verticesSetup a
  have hp : project (by decide : 5 ≤ 16) (by decide : 6 ≤ 48) b =
      AssignmentSeedRange.inputState
        (project (by decide : 5 ≤ 16) (by decide : 6 ≤ 48) b).regs D := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, b, PackingPlumbing.run, verticesSetup,
        PackingPlumbing.Op.next, a, extractionOutputState, inputState, hD,

        StackRoutines.copyStacks]
  obtain ⟨nv, hnv, hvt⟩ := AssignmentSeedRange.program_runsIn
    (project (by decide : 5 ≤ 16) (by decide : 6 ≤ 48) b).regs D
  let d := install (by decide : 5 ≤ 16) (by decide : 6 ≤ 48) b
    (AssignmentSeedRange.outputState D)
  have hcall : Eval verticesCall nv b d := by
    apply lowCall_eval
    rw [hp]
    exact hvt
  have hdstacks : d.stacks = fun i =>
      if i = 5 then AssignmentSeedRange.seedRecords D
      else (extractionOutputState input n c regs).stacks i :=
    vertices_call_stacks input n D c regs
  have hw : PackingPlumbing.Valid verticesSave d := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, verticesSave,
      PackingPlumbing.move]
  let e := PackingPlumbing.run verticesSave d
  have he : e = verticesOutputState input n D c e.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [e, PackingPlumbing.run, verticesSave, PackingPlumbing.move,
        PackingPlumbing.Op.next, hdstacks, extractionOutputState,
        inputState,
        StackRoutines.transferStacks]
  have hsetup : PackingPlumbing.cost verticesSetup a = 7 * D + 5 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, verticesSetup,
      a, extractionOutputState, inputState, hD]
  have hsave : PackingPlumbing.cost verticesSave d =
      6 * (AssignmentSeedRange.seedRecords D).length + 6 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, verticesSave,
      PackingPlumbing.move, PackingPlumbing.Op.next, hdstacks,
      StackRoutines.transferStacks, extractionOutputState, inputState]
    omega
  have hrun := (PackingPlumbing.eval verticesSetup a hv).seq
    (hcall.seq (PackingPlumbing.eval verticesSave d hw))
  refine ⟨PackingPlumbing.cost verticesSetup a + (nv + PackingPlumbing.cost verticesSave d),
    ?_, e.regs, ?_⟩
  · rw [hsetup, hsave]
    unfold verticesBudget
    omega
  · change Eval vertices _ a e at hrun
    rw [he] at hrun
    exact hrun

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def compareBlocks : Code := liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id (comparePorts 288 291)
def compareIndices : Code := liftCommand (GlobalBasisEntryCore.compare 0 1) 0 1 id (comparePorts 304 305)
def uncovered : Code := .seq compareIndices (.ite 7 one zero)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Measured staging and exact caller-store frames for the fixed source bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def emitterSize (a : Data) : ℕ :=
  (a.stacks 67).length+(a.stacks 308).length+(a.stacks 309).length+
  (a.stacks 310).length+(a.stacks 71).length+(a.stacks 311).length+
  (a.stacks 312).length+(a.stacks 313).length+(a.stacks 314).length+(a.stacks 47).length

def emitterStacks (a : Data) : Fin 320 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update a.stacks 280 (a.stacks 67)) 281 (a.stacks 308))
    282 (a.stacks 309)) 283 (a.stacks 310)) 284 (a.stacks 71)) 285 (a.stacks 311))
    286 (a.stacks 312)) 259 (a.stacks 313)) 266 (a.stacks 314)) 269 (a.stacks 47)

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def metadataStacks (a : Data) (mr mc : GlobalBasisMetadata.Metadata) : Fin 320 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update a.stacks 288 mr.block) 289 mr.typeCode)
      290 mr.rank) 291 mc.block) 292 mc.typeCode) 293 mc.rank

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def clearedStacks (a : Data) : Fin 320 → List Bool :=
  fun j=>if j∈cleanupPorts then [] else a.stacks j

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrameFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def deltaWord (a : Data) : List Bool :=
  if a.stacks 23=a.stacks 24 then a.stacks 314 else a.stacks 313

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Composition for the actual SourceBank. Premises about table and mismatch
execution are traces of their fixed native programs, not free callbacks. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def vectorState (a : Data) (rf : Fin 16 → Bool) (bits : List Bool) : Data :=
  ⟨rf,Function.update (Staging.result 0 1 stageTypesOps a).stacks 67 bits⟩

def branchState (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool) : Data :=
  ⟨rf,Function.update (Function.update (Staging.result 0 1 stageTypesOps a).stacks 67 bits) 71 indices⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cache and workspace invariants for the actual metadata dispatch. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The metadata return fields may be populated, while all disposable source
workspace is empty. Arithmetic services keep their separate native caches. -/
structure WorkReady (a : Data) : Prop where
  work : ∀ j∈cleanupPorts, (j.val < 288 ∨ 293 < j.val) → a.stacks j=[]
  temp : a.stacks 319=[]
  output : a.stacks 287=[]
  count : a.stacks 37=[]
  tableCount : a.stacks 64=[]
  tableAccum : a.stacks 65=[]
  low : ∀ j : Fin 320,j.val < 4 → a.stacks j=[]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBankCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial resource bounds for the concrete universal source
branch. Typed table entries contribute their actual d*B bit width. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

def universalBudget (p : Parameters r Q d) (S : ℕ) (u y : UniversalType r Q 1) : ℕ :=
  LayoutSourceValuesProgram.Native.tableBudget p.aWord.length p.R p.width.length
    (pairLength p.power) p.t d u y+
  (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
    UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
  14*S+224*sourceWorkspace p S+UniversalRowSourceBound.sourceBound (sourceWorkspace p S)+281

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native control branches for source-polynomial lookup. Every literal and
conditional is executed; the universal-branch premise is an actual trace of
that fixed command and is supplied by the native table/emitter composition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def LiteralReady (a : Data) : Prop :=
  a.stacks 319=[] ∧ a.stacks 315=[] ∧ a.stacks 316=[] ∧ a.stacks 287=[]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSourceMeaning
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

noncomputable def packedSourceValue {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row : Fin D) (i : ℕ) :
    Polynomial (p.model.O p.t) :=
  if hi : i < D then packedValue P p.rows row ⟨i,hi⟩ else 0

noncomputable def totalPackedSource {r Q d D : ℕ} (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : ℕ) :
    Polynomial (p.model.O p.t) :=
  if hr : row < D then packedSourceValue p P ⟨row,hr⟩ col else 0

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete source-table execution from physical layout metadata and ring
caches. No polynomial table or source-command service is an input. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open SubexponentialSAT.SubexpLiftRing

def nativeRowsBudget {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (s : Store) (v N f S : ℕ) (ps : List (ℕ × ℕ)) : ℕ :=
  let W := (p.R+1)*(d*baseWidth 3 p.t)
  let K := uniformRowBudget N ps (ps.length-1) (stagedSourceBudget p S)
    (Subexp.UniversalRowSourceBound.sourceLengthBound S) (p.R+1) d (baseWidth 3 p.t)
    ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) 21).length
    ((preparedSourceStore s (p.R+1) (d*baseWidth 3 p.t) ps v N f) 26).length
  LayoutSourceRowsProgramInitialize.budget (p.R+1) (d*baseWidth 3 p.t)+
    LayoutSourcePlanLookup.pairBudget v N f ps+N*(K+45*W+83)+
    2*(ps.idxOf (v,N+f))+23

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramNativeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A state-independent polynomial allowance for the complete source phase. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT LayoutProgram
open SubexponentialSAT.SubexpLiftRing
attribute [local simp] Fin.coe_ofNat_eq_mod

def nativeRowsPolynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ) : ℕ :=
  let W := (p.R+1)*(d*baseWidth 3 p.t)
  LayoutSourceRowsProgramInitialize.budget (p.R+1) (d*baseWidth 3 p.t)+
    1000*(4*S+1)^2+
    S*(rowBudgetPolynomial (stagedSourceBudget p S)
      (Subexp.UniversalRowSourceBound.sourceLengthBound S) (p.R+1) d (baseWidth 3 p.t) S+
      45*W+83)+2*S+23

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Per-node paid bootstrap: address multiplication, actual plan-record
counting, and construction of the integer interpolation coefficient cache. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def cacheState (regs : Fin 8 → Bool) (a r width : List Bool) (words : List (List Bool)) : State 8 24 :=
  LayoutProgram.IntegerCache.state regs a r width [] [] width words.flatten
    (List.replicate (r.length*width.length) false) (LayoutProgram.IntegerCache.denominatorWord r.length) []

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact state and cost of the paid per-node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog
namespace LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def bootState (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) : Data :=
  returned cacheRegs (by decide) cacheInputs cacheOutputs
    (countedState (addressState a ra r t) rd records) (cacheState rc height R width words)

def bootCost (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) : ℕ :=
  stageCost addressRegs (by decide) addressInputs addressOutputs a
      (Address.result ra r t) (Address.budget r t)+
  stageCost rowCountRegs (by decide) rowCountInputs rowCountOutputs (addressState a ra r t)
      (rowCountState rd records (List.replicate records.length true))
      (SubexponentialSAT.SubexpScopeCountSetup.countBudget records+1)+
  stageCost cacheRegs (by decide) cacheInputs cacheOutputs
      (countedState (addressState a ra r t) rd records)
      (cacheState rc height R width words) (cacheBound height R width)

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Initialization of one node's physical Cartesian head loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def nodeStart (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) : Data :=
  tupleInitialized (retainedState (bootState a ra rd rc r t records height R width words))

def initializeCost (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool)) : ℕ :=
  bootCost a ra rd rc r t records height R width words+
    retainCost (bootState a ra rd rc r t records height R width words)+8

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime source facts for the closed head setup. No cache output, matrix,
entry evaluator, or running-time witness is supplied in this interface. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

def Inputs.entryTime (s : Inputs) : ℕ :=
  LayoutFiberSumProgram.nativeTime s.r s.Q s.R s.width s.power s.height s.size s.lookupTime
def Inputs.columnLength (s : Inputs) : ℕ := s.D*(s.entryLength+2)
def Inputs.columnTime (s : Inputs) : ℕ :=
  1000*((LayoutOwnerFiberProgram.stream s.plans).length+s.n+1)^2+18*s.n+2*s.D+39+
    s.D*(s.entryTime+5*s.D+12+25000*((s.D+1)*(s.entryLength+2)+3)^2+9*(s.entryLength+2))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native entry cache is the actual output of the paid node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open RowSelectionProgram

def start (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) :=
  nodeStart a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def cacheLength (m : Model) (j : Fin 64) : ℕ :=
  if j=53 then m.val 50 else if j=52 then m.val 46 else if j=51 then m.val 29 else m.len j

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendNumericRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


def numericInput (ambient clauses : List Bool) (k free occ arity factors mass : ℕ) : Input :=
  ⟨BinaryArithmetic.toNat ambient,free,BinaryArithmetic.toNat clauses,k,factors,occ,arity,mass⟩

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Joined per-query core. Mathematical values below describe physical input
words and computed outputs; they are not extra machine inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.input (q : Query) (k : ℕ) : LeafParametersProgram.Input :=
  numericInput q.ambient q.modulus k (totals q.scopeRows q.forward).free
    (totals q.scopeRows q.forward).occurrence (completedArity q.scopeRows q.forward)
    (q.scopeRows.length+(totals q.scopeRows q.forward).uncovered)
    (totals q.scopeRows q.forward).incidences

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryPackingInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The packing problem is determined by the physically measured query.
In particular its incidence count is the same native mask scan exported by
the frontend, including neutral factors for uncovered low variables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

noncomputable def packingProblem (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) : PackingCallerProgram.Problem where
  scopes := q.scopeRows
  n := BinaryArithmetic.toNat q.ambient
  mask := q.forward
  mask_le := by simp [LeafQueryFrontend.Query.forward,LeafQueryFrontend.highMask]
  r := (produce (q.input k)).r
  Q := (produce (q.input k)).Q
  s := (produce (q.input k)).epsilonDen
  hr := lt_of_lt_of_le (by decide : 0 < 2) (produce_r_ge_two _)
  hQ := by have h := hg.2.2.2.2.2.2.1; omega
  hs := produce_epsilonDen_pos _ hg.2.2.2.1

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafPackingFiberBoundsQuery
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! No raw-fiber hypothesis is needed for a produced query: its actual scope
rows are deduplicated, and its parameter fields are the actual native scan. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsProgram LeafQueryFrontend

 theorem query_owner_fiber_le (q : Query) (k : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (v : Fin (LeafProgram.Query.packingProblem q k hg).n) :
    let p := LeafProgram.Query.packingProblem q k hg
    (Finset.univ.filter fun i : Semantics.Incidences p.scopes p.mask =>
      Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ (q.input k).occurrence := by
  exact owner_fiber_le _ _ _ _ v

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankMagnitude
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual raw owner-fiber length controls separately stored signed
components, so the executed shift is bounded without canonical signs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open PackingCallerProgram LeafParametersProgram BucketProgram.ProducedRank

 theorem query_fiber_length_le (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) (v : Fin (LeafProgram.Query.packingProblem q k hg).n) :
    (LayoutOwnerFiberProgram.fiberIndices v.val 0
      (PackingIncidenceInput.Semantics.nativeEntries q.scopeRows q.forward)).length ≤
      (q.input k).occurrence := by
  rw [show PackingIncidenceInput.Semantics.nativeEntries q.scopeRows q.forward=
    PackingIncidenceInput.Semantics.nativeEntries (LeafProgram.Query.packingProblem q k hg).scopes
      (LeafProgram.Query.packingProblem q k hg).mask from rfl]
  rw [actual_fiber_length]
  exact LeafPackingFiberBounds.query_owner_fiber_le q k hg v

 def queryHeight (q : LeafQueryFrontend.Query) (k : ℕ) : ℕ :=
  2*(q.input k).occurrence*(8*(produce (q.input k)).Q)^(2*(produce (q.input k)).R)

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end


