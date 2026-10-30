-- Prove2me | Definitions.Def_OAIQ081S158
-- name    : OAIQ081S158
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:02:44.692492+00:00
-- url     : https://prove2.me/theorems/c359af9a-280a-4bc9-81d2-0303260d74fd
-- title:
--   Definitions bundle OAIQ081S158 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 70 declarations of OpenAI's Lean: 41 definitions, 3 inductive types or structures and 26 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.countedState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.initializeCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.rowCountState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete.residualValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.indicatorPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Count.reconstruct`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.HashInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.indicator`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.productBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseFinished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.clauseResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.high`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.indicatorBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.indicatorFinished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.FactorServices.readied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Incidence.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Incidence.exportCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Incidence.exported`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Incidence.stageCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Incidence.staged`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.rawHash`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.sourceTerms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics.codeDigits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.GeneratedCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource.GeneratedCode.code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Valid`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.inputLengths`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.numericCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.CoreOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.constantsPhase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.nodesPhase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.outer` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoot`, `SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcreteEmbedding`, `SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsDenote`, `SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsFactors`, `SubexponentialSAT_SqrtLog_LeafProgramCount`, `SubexponentialSAT_SqrtLog_LeafProgramFactor`, `SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsServices`, `SubexponentialSAT_SqrtLog_LeafProgramFactorFinish`, `SubexponentialSAT_SqrtLog_LeafProgramFactorInput`, `SubexponentialSAT_SqrtLog_LeafProgramFactorServices`, `SubexponentialSAT_SqrtLog_LeafProgramFactorServicesBase`, `SubexponentialSAT_SqrtLog_LeafProgramIncidence`, `SubexponentialSAT_SqrtLog_LeafProgramIndicator`, `SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics`, `SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCode`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedFactorBase`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCore`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCoreBound`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_PackingCallerProgramStage`, `SubexponentialSAT_SqrtLog_ReconstructionProgramNative`, `SubexponentialSAT_SqrtLog_RingProgramTableSemantics`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S139`, `OAIQ081S142`, `OAIQ081S143`, `OAIQ081S144`, `OAIQ081S145` and `OAIQ081S146` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S168`, `OAIQ081S169`, `OAIQ081S170`, `OAIQ081S171` and `OAIQ081S172`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.hashWork_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.indicatorBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.markedWork_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.result_good`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.expanded_hash_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.hashWork_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.indicatorBudget_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.markedWork_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.result_good`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues.serialized_values_of_fourth_power`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_denote_at`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics.selectedFactor_good`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.expanded_hash_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.hash_value_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_tail_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.query_bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafScopeInputBounds.scope_cost_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S142
import Definitions.Def_OAIQ081S143
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S145
import Definitions.Def_OAIQ081S146

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

def rowCountState (regs : Fin 8 → Bool) (records : List (List Bool)) (count : List Bool) : State 8 15 :=
  ⟨regs,fun i => if i=1 then SubexponentialSAT.Encoding.encodeList id records else if i=2 then count else []⟩

def initializeCache : Code := stage LayoutProgram.IntegerCache.program cacheRegs (by decide)
  cacheInputs cacheOutputs

def boot : Code := .seq initializeAddress (.seq countRows initializeCache)

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

def countedState (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool)) : Data :=
  returned rowCountRegs (by decide) rowCountInputs rowCountOutputs a
    (rowCountState regs records (List.replicate records.length true))

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def runtimeBound (x : Input) (inputLengths : Fin 8 → ℕ) : ℕ :=
  Circuit.budget code (initialModel x inputLengths)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayoutReady -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout

open Circuit Bank BinaryArithmetic

theorem prefix_values (x : Input) (l : Fin 8 → ℕ) :
    (result prefixCode (initialModel x l)).val 13 = Asymptotic.L x.freeCount ∧
    (result prefixCode (initialModel x l)).val 18 = Asymptotic.layoutR x.freeCount ∧
    (result prefixCode (initialModel x l)).val 21 = Asymptotic.layoutQ x.freeCount := by
  let m := result earlyCode (initialModel x l)
  have h13 : m.val 13 = Asymptotic.L x.freeCount := by
    simp [m,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,BinaryArithmetic.toNat,bitVal]
  have h18 : m.val 18 = Asymptotic.layoutR x.freeCount := by
    simp [m,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,
      BinaryArithmetic.toNat,bitVal,pow_two]
  rw [prefixCode,result_append]
  constructor
  · rw [result_value_frame quotientCode _ 13]
    · exact h13
    · decide
  constructor
  · rw [result_value_frame quotientCode _ 18]
    · exact h18
    · decide
  · simp [result,next,value,output,
      initialModel,initialValues,
      Asymptotic.layoutQ,Asymptotic.layoutDen,Asymptotic.layoutR,
      Asymptotic.s,Asymptotic.w,Asymptotic.L,pow_two]

theorem prefix_eight (x : Input) (l : Fin 8 → ℕ) :
    (result prefixCode (initialModel x l)).val 8 = 2 := by
  rw [prefixCode,result_append]
  rw [result_value_frame quotientCode _ 8]
  · simp [result,next,value,output,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal]
  · decide

set_option maxHeartbeats 3200000 in
theorem val_eq (x : Input) (l : Fin 8 → ℕ) :
    (model x l).val 13 = Asymptotic.L x.freeCount ∧
    (model x l).val 14 = Asymptotic.w x.freeCount ∧
    (model x l).val 17 = Asymptotic.s x.freeCount ∧
    (model x l).val 18 = Asymptotic.layoutR x.freeCount ∧
    (model x l).val 21 = Asymptotic.layoutQ x.freeCount ∧
    (model x l).val 25 = 32*x.occurrence*Asymptotic.layoutR x.freeCount*
      Asymptotic.L x.freeCount^2 ∧
    (model x l).val 29 = Asymptotic.layoutCutoff x.freeCount x.occurrence ∧
    (model x l).val 31 = Asymptotic.layoutR x.freeCount^(2*Asymptotic.layoutQ x.freeCount) := by
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L, BinaryArithmetic.toNat,bitVal]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w, BinaryArithmetic.toNat,bitVal]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s, BinaryArithmetic.toNat,bitVal,pow_two]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,
      BinaryArithmetic.toNat,bitVal,pow_two]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,Asymptotic.layoutQ,
      Asymptotic.layoutDen, BinaryArithmetic.toNat,bitVal,pow_two]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,
      BinaryArithmetic.toNat,bitVal,pow_two,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]
  constructor
  · simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
      Asymptotic.L,Asymptotic.w,Asymptotic.s,Asymptotic.layoutR,Asymptotic.layoutQ,
      Asymptotic.layoutDen,Asymptotic.layoutCutoff,Asymptotic.layoutEnergy,
      BinaryArithmetic.toNat,bitVal,pow_two]
    congr 1
    ring_nf
  · rw [model,code,result_append]
    rw [result_value_frame tailCode _ 31]
    · rw [coreCode,result_append]
      obtain ⟨_,hr,hq⟩ := prefix_values x l
      have h8 := prefix_eight x l
      rw [finishCode,result_append]
      have hr' : (result heavyCode (result prefixCode (initialModel x l))).val 18 =
          Asymptotic.layoutR x.freeCount := by
        rw [result_value_frame heavyCode _ 18]
        · exact hr
        · decide
      have hq' : (result heavyCode (result prefixCode (initialModel x l))).val 21 =
          Asymptotic.layoutQ x.freeCount := by
        rw [result_value_frame heavyCode _ 21]
        · exact hq
        · decide
      have h8' : (result heavyCode (result prefixCode (initialModel x l))).val 8 = 2 := by
        rw [result_value_frame heavyCode _ 8]
        · exact h8
        · decide
      let mh := result heavyCode (result prefixCode (initialModel x l))
      change mh.val 18 = Asymptotic.layoutR x.freeCount at hr'
      change mh.val 21 = Asymptotic.layoutQ x.freeCount at hq'
      change mh.val 8 = 2 at h8'
      change (result powerCode mh).val 31 =
        Asymptotic.layoutR x.freeCount ^ (2 * Asymptotic.layoutQ x.freeCount)
      simp [result,next,value,output,hr',hq',h8']
    · decide

theorem model_core_values (x : Input) (l : Fin 8 → ℕ) :
    (model x l).val 13 = (produce x).L ∧
    (model x l).val 14 = (produce x).w ∧
    (model x l).val 17 = (produce x).s ∧
    (model x l).val 18 = (produce x).r ∧
    (model x l).val 21 = (produce x).Q ∧
    (model x l).val 25 = (produce x).epsilonDen ∧
    (model x l).val 29 = (produce x).R ∧
    (model x l).val 31 = (produce x).N := val_eq x l

theorem model_inputs (x : Input) (l : Fin 8 → ℕ) (i : Fin 8) :
    (model x l).val (i.castAdd 56)=initialValues x (i.castAdd 56) := by
  fin_cases i <;> simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues]

theorem model_precision (x : Input) (l : Fin 8 → ℕ) (hm : x.clauses≠0) :
    (model x l).val 33 = (produce x).t := by
  simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
    produce,precision,size_eq_log2_add_one hm,BinaryArithmetic.toNat,bitVal,Nat.add_assoc]

theorem model_degree (x : Input) (l : Fin 8 → ℕ) (hQ : (produce x).Q≠0) :
    (model x l).val 34 = (produce x).d := by
  have h := size_eq_log2_add_one hQ
  simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
    produce,extensionDegree,Asymptotic.layoutQ,Asymptotic.layoutDen,
    Asymptotic.layoutR,Asymptotic.s,Asymptotic.w,Asymptotic.L,BinaryArithmetic.toNat,bitVal,
    pow_two,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] at h ⊢
  omega

theorem model_fieldCard (x : Input) (l : Fin 8 → ℕ) (hQ : (produce x).Q≠0) :
    (model x l).val 35 = fieldCard x := by
  rw [fieldCard,← model_degree x l hQ]
  simp [model,code,coreCode,tailCode,result,next,value,output,initialModel,initialValues,
    BinaryArithmetic.toNat,bitVal]

theorem model_jet (x : Input) (l : Fin 8 → ℕ)
    (hm : x.clauses≠0) (hQ : (produce x).Q≠0) :
    (model x l).val 42 = (produce x).J := by
  have hpos : 1 ≤ (produce x).Q := Nat.one_le_iff_ne_zero.mpr hQ
  have hsafe := Nat.sub_add_cancel hpos
  rcases model_core_values x l with ⟨_,_,_,_,hQ',_,hR,_⟩
  have hf := model_inputs x l 5
  have hw := model_inputs x l 6
  let m₀ := result coreCode (initialModel x l)
  have h0 : m₀.val 0 = x.ambient := by
    dsimp [m₀]
    rw [result_value_frame coreCode _ 0]
    · rfl
    · decide
  have h2 : m₀.val 2 = x.clauses := by
    dsimp [m₀]
    rw [result_value_frame coreCode _ 2]
    · rfl
    · decide
  have h8 : m₀.val 8 = 2 := by
    simp [m₀,coreCode,result,next,value,output,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal]
  have h9 : m₀.val 9 = 3 := by
    simp [m₀,coreCode,result,next,value,output,initialModel,initialValues,
      BinaryArithmetic.toNat,bitVal]
  rw [model,code,result_append] at hQ' hR hf hw ⊢
  simp [tailCode,result,next,value,output] at hQ' hR hf hw ⊢
  change m₀.val 21 = _ at hQ'
  change m₀.val 29 = _ at hR
  change m₀.val 5 = _ at hf
  change m₀.val 6 = _ at hw
  change m₀.val 6 * m₀.val 29 *
      (m₀.val 8 * m₀.val 5 +
        m₀.val 9 * (m₀.val 0 + (Nat.log2 (m₀.val 2) + 1)) + 1) /
      (m₀.val 21 - 1 + 1) + 1 = (produce x).J
  rw [hQ',hR,hf,hw,h0,h2,h8,h9]
  simp [initialValues]
  rw [hsafe]
  simp [produce,precision,size_eq_log2_add_one hm]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Layout


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramGuardSetup -/


namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

def runtimeBound (x : Input) (l : Fin 8 → ℕ) :=
  Layout.runtimeBound x l+Circuit.budget GuardSetup.code (Layout.model x l)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Prepared


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramExecute -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Validity and storage bounds for the actual raw dictionaries produced by
native hash-row execution. No canonical-output premise is used. -/


/-! Denotation of the concrete raw row recurrence used by the native program. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

def sourceTerms {R : Type*} {n B d : ℕ} (f : RingProgram.Code (Word B) d → R)
    (ws : List (Row.WeightedClause n B d)) : SparseRow (Fin n) R :=
  ws.map (fun w => (f w.scalar,w.literals))

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics


/-! Instantiation at the actual supplied-polynomial unramified ring. -/


/-! Original literal identifiers remain unchanged when the native dictionaries
carry padded jets from the free coordinates of a branch. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIndicator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A closed native sparse-hash indicator service. It first interprets the
actual inline weighted-clause row and then applies the computed idempotent
coefficient tape. The resulting indicator is never supplied as input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Indicator

attribute [local simp] Fin.addCases

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

def rawHash {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (ws : List (Row.WeightedClause n (baseWidth p t) d)) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  DynamicFold.value (Row.value p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J) ws []

def result {p t n d : ℕ} [Fact p.Prime] (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) : Raw (p:=p) (t:=t) (n:=n) (d:=d) :=
  IdempotentApplyProgram.applied ctx minus (rawHash ctx minus one incidence ws) one digits

end SubexponentialSAT.SqrtLog.LeafProgram.Indicator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsFactors
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected factor map matches the runtime dispatcher: hashes first,
one optional direct marked clause, then skipped neutral IDs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open NativeSemantics
open IdempotentApplyProgram.Steps (Context)

variable {p t n d : ℕ} [Fact p.Prime]

def selectedFactor (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d) (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : ℕ → Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n)))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t)))
    (id : ℕ) : Option (Raw (p:=p) (t:=t) (n:=n) (d:=d)) :=
  if h : id < hashes.length then
    some (Indicator.result ctx minus one (incidence id) hashes[id] digits)
  else if marked && decide (id = hashes.length) then
    some (DynamicFold.value
      (Clause.step p t ctx.modulus ctx.cache ctx.table minus one (incidence id) ctx.u ctx.J)
      clause one)
  else none

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentSemanticsDenote
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-scoped semantics of each actual selected factor, followed by the
canonical product in the selected ID order. The marked clause is not lifted
through the hash idempotent. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators

variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

noncomputable def indicatorPolynomial (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (H : Squarefree.Jet (Fin n) R) : Squarefree.Jet (Fin n) R :=
  ∑ s : Fin t,
    (Squarefree.Sparse.atom (IdempotentApplyProgram.Multiplier.uKey n) 1)^s.val *
      (IdempotentProgram.digitPolynomial (RingProgram.scalarRing p t ctx.modulus ctx.cache)
        code s).eval₂ ((Moments.ringScalar (V:=Fin n)).comp scalar) H *
      IdempotentProgram.hValue H^s.val

noncomputable def selectedValue (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jet : ℕ → Fin n → Squarefree.Jet (Fin n) R)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) :
    Squarefree.Jet (Fin n) R :=
  if h : id < hashes.length then
    indicatorPolynomial ctx scalar code
      (MvPolynomial.eval (jet id) (rowPolynomial (scalarJet (V:=Fin n))
        (sourceTerms (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache)
          scalar basis) hashes[id])))
  else if marked && decide (id = hashes.length) then
    MvPolynomial.eval (jet id) (clausePolynomial (R := Squarefree.Jet (Fin n) R) clause)
  else 1

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def outer : WideCode := UnaryForPrograms.forCmd outerPorts row

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeSemanticsCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The code-dependent expressions emitted by the actual assignment fold
are connected to the scalar U-expansion, without evaluating U at one. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open IdempotentApplyProgram.Steps (Context)
open AssignmentSemantics
noncomputable section

variable {p t n d : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]

def codeDigits (ctx : Context p t n d) (scalar : ZMod (p^t) →+* R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t)) : Fin t → R[X] :=
  fun s => (IdempotentProgram.digitPolynomial
    (RingProgram.scalarRing p t ctx.modulus ctx.cache) code s).map scalar

end
end SubexponentialSAT.SqrtLog.LeafProgram.NodeSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcreteEmbedding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Selected factors may have ambient literal IDs but free formal variables.
Embedding is performed on the polynomial itself, never through a chosen
stored representation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open Polynomial _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree NodeSemantics
open SubexponentialSAT SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps (Context)
open scoped BigOperators

variable {V W I R : Type*} [DecidableEq V] [DecidableEq W] [CommRing R]

variable {p t n d : ℕ} [Fact p.Prime]

def residualValue (ctx : Context p t n d)
    (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
    (code : RingProgram.Code (RingProgram.ScalarCode p t) (3*t))
    (jfree : ℕ → Fin n → Jet V R)
    (hashes : List (List (Row.WeightedClause n (baseWidth p t) d)))
    (marked : Bool) (clause : List (SAT.Literal (Fin n))) (id : ℕ) : Jet V R :=
  if h : id < hashes.length then
    indicatorJet t (codeDigits ctx scalar code)
      (MvPolynomial.eval (jfree id) (rowPolynomial (R:=Jet V R) scalarJet
        (NativeSemantics.sourceTerms
          (RingProgram.denote (RingProgram.scalarRing p t ctx.modulus ctx.cache) scalar basis)
          hashes[id])))
  else if marked && decide (id=hashes.length) then
    MvPolynomial.eval (jfree id) (clausePolynomial (R:=Jet V R) clause)
  else 1

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One finite instruction table for arbitrary dynamic coefficient degree,
ring precision, node count, and jet order. All such parameters reside on
input tapes. The scalar and polynomial services here are concrete programs. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls

/-- Fixed arithmetic stage used by every outer-node iteration. -/
abbrev middle : Cmd 16 320 :=
  Middle.command localCode HornerProgram.Services.multiply HornerProgram.Services.add

/-- Cache preparation, physical initialization, node traversal, and cleanup. -/
abbrev command : Cmd 16 320 := .seq Entry.prepare (ReconstructionProgram.controller middle)

abbrev program : Program 16 320 (size command + 1) := compiled command 256 261

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One closed native count-recovery table: Hermite reconstruction over the
computed ring, integer readback, and reclamation of the two CRT entry caches.
Node-jet production and its semantic theorem are composed at the caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev reconstruct : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram ReconstructionProgram.Native.program crtRegisters crtStacks)

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The selected-factor incidence service with a concrete source generator.
All ring/layout inputs are copied from persistent masters, and the complete
private worker is reclaimed after exporting the actual lookup table. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Incidence
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
abbrev Data := State 16 768

def staged (a : Data) : Data := SourceControls.cutoffState (copyManyState pairs a)
def stageCost (a : Data) : ℕ := copyManyCost pairs a + 7*(a.stacks 138).length+7

def exported (a : Data) : Data := clearManyState workerPorts (copyState 561 62 a)
def exportCost (a : Data) : ℕ := 7*(a.stacks 561).length+5+
  clearManyCost workerPorts (copyState 561 62 a)

end SubexponentialSAT.SqrtLog.LeafProgram.Incidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed per-assignment factor evaluation. Factors are dispatched by runtime
ID; hash rows are expanded and tested by the computed idempotent, the marked
clause is multiplied directly, and added neutral factors contribute one.
Every operation below is an actual finite instruction table or native loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls

def indicator : Code := .seq indicatorReady
  (.call (ProgramLinking.liftProgram Indicator.program nativeRegisters indicatorStacks))

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid cleanup and multiplication after a real factor service. The running
product remains on151 and all source/cache tapes are framed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native

def productBudget (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t)) (u J : ℕ)
    (seed factor : List (MomentsProgram.Product.Entry n (baseWidth p t) d)) : ℕ :=
  let result := MomentsProgram.Product.run p t M cache table u J seed factor []
  18*(MomentsProgram.Product.bytes seed).length+
    20*(MomentsProgram.Product.bytes factor).length+18*(MomentsProgram.Product.bytes result).length+
    MomentsProgram.Product.work p t M cache table u J seed factor []+54

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorServicesBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact framing tools for the fixed wide indicator and marked-clause calls.
The functions below only describe states; executable code remains Factor's
already defined finite service tables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT BitProgram StructuredCalls
open HashCircuitProgram HashCircuitProgram.Native

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

abbrev Data := State 40 768

def high (map : Fin 96 → Fin 768) (a : Data) : Fin 40 → List Bool :=
  fun i => a.stacks (map (Memory.highPort i))

def readied (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 true) 2 false,a.stacks⟩

noncomputable def indicatorFinished (a : Data) (rr : Fin 8 → Bool) (hash result : List Bool) : Data :=
  ⟨Function.extend Factor.nativeRegisters rr (readied a).regs,
    Function.update (Function.update (Function.update a.stacks 64 []) 67 result) 68 hash⟩
noncomputable def clauseFinished (a : Data) (rr : Fin 8 → Bool) (result : List Bool) : Data :=
  ⟨Function.extend Clause.callerRegisters rr a.regs,
    Function.update (Function.update a.stacks 63 []) 67 result⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual wide factor service calls, including the indicator's three parser
register writes, compiled returns, and exact caller frame. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

variable {p t n d : ℕ} [Fact p.Prime]

def indicatorBudget (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode p t))) : ℕ :=
  11+DynamicFold.work Row.payload
    (Row.value p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J)
    (Row.cost p t ctx.modulus ctx.cache ctx.table minus one incidence
      (List.replicate d true) ctx.u ctx.J entries) ws []+
    IdempotentApplyProgram.applicationBudget ctx minus (Indicator.rawHash ctx minus one incidence ws) one digits

def clauseBudget (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool)) (ls : List (SAT.Literal (Fin n))) : ℕ :=
  7*(Product.bytes one).length+9+
    DynamicFold.work HashCircuitProgram.Native.Clause.literalBits
      (HashCircuitProgram.Native.Clause.step p t ctx.modulus ctx.cache ctx.table minus one incidence ctx.u ctx.J)
      (HashCircuitProgram.Native.Clause.cost p t ctx.modulus ctx.cache ctx.table minus one incidence
        (List.replicate d true) ctx.u ctx.J entries) ls one

def clauseResult (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d)) (ls : List (SAT.Literal (Fin n))) :=
  DynamicFold.value (HashCircuitProgram.Native.Clause.step p t ctx.modulus ctx.cache ctx.table
    minus one incidence ctx.u ctx.J) ls one

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBoundsServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bounds for the measured native factor services and their paid cleanup.
The retained-key capacity remains an explicit argument of every envelope. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native MomentsProgram
open IdempotentApplyProgram.Steps NativeSemantics

theorem indicator_good_iff {n B d u J : ℕ} {vars : Finset (Fin n)}
    {a : List (Product.Entry n B d)} :
    IdempotentApplyProgram.Bounds.Good vars u J a ↔ Good vars u J a :=
  ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.valid,h.nodup⟩⟩

end SubexponentialSAT.SqrtLog.LeafProgram.FactorBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical factor inputs that are retained by the incidence producer. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

structure HashInput {t n d : ℕ} (ctx : Context 3 t n d)
    (minus : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 t)))
    (b : ℕ) (a : Data) : Prop where
  raw : a.stacks 154=(HashInputProgram.Loop.rawInput b terms).reverse
  formula : a.stacks 700=ExecQuantitativeSparsify.encodeRawFormula source
  width : (a.stacks 708).length=b
  modulus : BinaryArithmetic.toNat (a.stacks 707)=(HashInputProgram.Expansion.encodedClauses source).length
  ringShape : (a.stacks 280).length=d*baseWidth 3 t
  output : a.stacks 64=[]
  expand : ∀ i ∈ Expansion.scratch,a.stacks i=[]
  work358 : a.stacks 358=[]
  work359 : a.stacks 359=[]
  low : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=IdempotentApplyProgram.Steps.low ctx i
  one : a.stacks 69=Product.bytes one
  minus : a.stacks 76=RingProgram.flat minus
  tape : a.stacks 143=IdempotentApplyProgram.triplesTape digits
  shape : (a.stacks 88).length=n
  work : ∀ i ∈ FactorServices.indicatorScratch,a.stacks (indicatorStacks i)=[]
  seed : a.stacks 151=Product.bytes seed
  temporary : a.stacks 159=[]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem advance_decode (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (hz : wordValue p t zeroWord = 0) (hm : wordValue p t minusOne = -1)
    (c : List.Vector (Word (baseWidth p t)) d) (v : VectorData (baseWidth p t) d)
    (hv : TailCorrect v) :
    (fun i => wordValue p t ((advance p t M zeroWord minusOne c v).coefficients.get i)) =
      IrreducibleSearch.mulX (fun i => wordValue p t (c.get i))
        (fun i => wordValue p t (v.coefficients.get i)) := by
  apply List.ofFn_injective
  change List.ofFn ((wordValue p t) ∘ (advance p t M zeroWord minusOne c v).coefficients.get) = _
  rw [← List.map_ofFn, listOfFn_get]
  change (outputWords p t M v.last minusOne (c.val.zip v.coefficients.val) zeroWord).map _ = _
  rw [outputWords_correct p t M v.last minusOne hm, hz]
  rw [← listOfFn_get c, ← listOfFn_get v.coefficients, zip_ofFn, List.map_ofFn]
  have ht : wordValue p t v.last = IrreducibleSearch.entry
      (fun i => wordValue p t (v.coefficients.get i)) (d-1) := by
    rw [tailCorrect_get hd v hv]
    simp [IrreducibleSearch.entry, show d-1 < d by omega]
  rw [ht]
  exact IrreducibleSearch.companionScan_eq_mulX _ _


theorem initialData_decode (p t : ℕ) [Fact p.Prime] {d : ℕ}
    (oneWord zeroWord : Word (baseWidth p t))
    (ho : wordValue p t oneWord = 1) (hz : wordValue p t zeroWord = 0) :
    (fun i => wordValue p t ((initialData d oneWord zeroWord).coefficients.get i)) =
      IrreducibleSearch.oneVector d := by
  funext i
  rw [initialData_get]
  simp only [IrreducibleSearch.oneVector]
  split <;> simp_all


theorem powerData_decode (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (oneWord zeroWord minusOne : Word (baseWidth p t))
    (ho : wordValue p t oneWord = 1) (hz : wordValue p t zeroWord = 0)
    (hm : wordValue p t minusOne = -1) (c : List.Vector (Word (baseWidth p t)) d) (n : ℕ) :
    (fun i => wordValue p t ((iterData p t M zeroWord minusOne c n
      (initialData d oneWord zeroWord)).coefficients.get i)) =
      IrreducibleSearch.powerVector (fun i => wordValue p t (c.get i)) n := by
  induction n with
  | zero =>
    simpa only [iterData, IrreducibleSearch.powerVector, IrreducibleSearch.cacheVector_eq] using
      initialData_decode p t oneWord zeroWord ho hz
  | succ n ih =>
    rw [iterData_succ, advance_decode p t M hd zeroWord minusOne hz hm c _
      (iterData_tailCorrect p t M hd zeroWord minusOne c n _
        (initialData_tailCorrect hd oneWord zeroWord)), ih]
    simp only [IrreducibleSearch.powerVector, IrreducibleSearch.cacheVector_eq]

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/- Component: LeafRingSetupProgramScalar.lean -/

/-! The first concrete stage of ring setup.  Only the runtime binary
precision is supplied.  The generated scalar cache remains exposed while
the extension-ring table and constants are built.  The idempotent producer
later uses a separately framed preparation, with its own charged cost. -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing


/-- Only the unary degree is initially present in the local search workspace.
The caller's modulus, scalar cache and width tapes lie outside that workspace. -/
theorem searchCall_eval (a : Data) (depth : List Bool) (hd : 0 < depth.length)
    (ha : projectState (registers 22 (by decide)) search a =
      IrreducibleSearchBootstrap.input depth) :
    ∃ n ≤ IrreducibleSearchBootstrap.totalCost depth.length,
      ∃ out : StructuredProgram.State 22 28,
        Eval searchCall n a (embedState (registers 22 (by decide)) search a out) ∧
        out.stacks 13 = IrreducibleSearchProgram.coefficientArray
          (List.ofFn (IrreducibleSearch.data hd).coefficients) ∧
        IrreducibleSearchCandidateControl.Ready depth.length depth (false::depth) [] out ∧
        out.stacks 25 = [] ∧
        (out.stacks 12).length ≤ IrreducibleSearchBootstrap.totalCost depth.length := by
  obtain ⟨out,ho,hr,h25,n,hn,he⟩ :=
    IrreducibleSearchBootstrap.searchProgram_runsIn depth hd
  have hg := Subexp.SequentialProgram.trace_stack_length_le he (12 : Fin 28)
  have hw : (out.stacks 12).length ≤ n := by
    simpa [IrreducibleSearchBootstrap.input, StructuredProgram.ioState,
      StructuredProgram.State.withPC] using hg
  refine ⟨n,hn,out,?_,?_,hr,h25,hw.trans hn⟩
  · exact eval_call_from_state IrreducibleSearchBootstrap.searchProgram
      (registers 22 (by decide)) search a (registers_injective 22 (by decide))
      search_injective (ha.symm ▸ he)
  · simpa only [IrreducibleSearch.data_coefficients,
      IrreducibleSearchProgram.coefficientArray_ofFn] using ho

/-- The raw search's scratch certificate is exactly sufficient for the
padding routine once the separately generated scalar-width word is copied
onto local12.  This statement is only a state-description lemma; the copy
itself is paid by `overwrite_eval`. -/
theorem search_padding_ready (depth : List Bool)
    (raw : StructuredProgram.State 22 28)
    (hr : IrreducibleSearchCandidateControl.Ready depth.length depth (false::depth) [] raw)
    (h25 : raw.stacks 25 = []) (width : List Bool) (r : Fin 22 → Bool) :
    RingCoefficientLiftProgram.SearchReady
      (⟨r,Function.update raw.stacks 12 width⟩ : StructuredProgram.State 22 28) := by
  obtain ⟨h15,h21,h23,h26⟩ := hr.scratch
  exact ⟨by simpa using h23,by simpa using h15,by simpa using h25,
    by simpa using h26,by simpa using h21⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramTable.lean -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/

/-! Physical node generation and record framing at the ring-setup ports. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpLiftRing

theorem nodesCall_eval (a : Data) (r : Fin 8 → Bool) (t : ℕ) (ht : 0 < t)
    (rank arity : List Bool)
    (ha : projectState (registers 8 (by decide)) nodes a =
      SubexpFieldRowPreparation.data r (List.replicate (baseWidth 3 t) false)
        rank arity [] [] []) :
    ∃ n ≤ RingNodeProgram.budget (baseWidth 3 t) rank.length arity.length
      (BinaryArithmetic.toNat rank)+5, ∃ rf finalRank,
      Eval nodesCall n a
        (embedState (registers 8 (by decide)) nodes a
          (SubexpFieldRowPreparation.data rf
            (true :: true :: List.replicate (baseWidth 3 t-2) false)
            finalRank arity [] []
            ((nodeWords t arity.length (BinaryArithmetic.toNat rank)).map RingProgram.flat).flatten)) ∧
      CounterPrograms.value finalRank = 0 ∧ finalRank.length = rank.length := by
  obtain ⟨rf,last,⟨n,hn,he⟩,hv,hl⟩ := RingNodeProgram.preparedProgram_nodes r t ht rank arity
  have he' := eval_call_from_state RingNodeProgram.preparedProgram
    (registers 8 (by decide)) nodes a (registers_injective 8 (by decide)) nodes_injective
    (ha.symm ▸ he)
  refine ⟨n,hn,rf,last,?_,hv,hl⟩
  simpa only [nodesCall,nodeWords,List.map_map,List.flatMap_def,Function.comp_def] using he'

theorem nodeFramesCall_eval (a : Data) (r : Fin 5 → Bool) (t d Q : ℕ)
    (width : List Bool) (hw : width.length = d * baseWidth 3 t)
    (ha : projectState (registers 5 (by decide)) nodeFramePorts a =
      SubexpTaylorFrames.state r
        (SubexpTaylorFrames.data width Q
          (((nodeWords t d Q).map RingProgram.flat).flatten) [])) :
    ∃ rf, Eval nodeFramesCall (Q*(28*width.length+33)+11) a
      (embedState (registers 5 (by decide)) nodeFramePorts a
        (SubexpTaylorFrames.state rf
          {SubexpTaylorFrames.data width 0 [] [] with
            output := Encoding.encodeList id ((nodeWords t d Q).map RingProgram.flat)})) := by
  obtain ⟨rf,he⟩ := LeafProgram.NodeFrames.ringWords_trace width hw (nodeWords t d Q) r
  simp only [nodeWords_length] at he
  exact ⟨rf,eval_call_from_state SubexpTaylorFrames.program
    (registers 5 (by decide)) nodeFramePorts a (registers_injective 5 (by decide))
    nodeFramePorts_injective (ha.symm ▸ he)⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramConstants.lean -/

/-! Actual constant-vector and idempotent calls in the setup workspace. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing StackRoutines

/-- The field polynomial and its lifted bytes are produced by one real
search/copy/padding execution.  The clearing cost of the search's old width
scratch is bounded by the actual search trace. -/
theorem searchAndPad_eval (a : Data) (depth : List Bool) (hd : 0 < depth.length)
    (t : ℕ) (ht : 0 < t)
    (ha : projectState (registers 22 (by decide)) search a =
      IrreducibleSearchBootstrap.input depth)
    (hw : (a.stacks 202).length=baseWidth 3 t) (h639 : a.stacks 639=[]) :
    ∃ n ≤ 3*IrreducibleSearchBootstrap.totalCost depth.length +
        7*baseWidth 3 t+depth.length*(28*t+14)+15,
      ∃ e : Data, Eval searchAndPad n a e ∧
        e.stacks 441=RingProgram.flat (RingProgram.liftCoefficientsRun t
          (IrreducibleSearch.data hd).coefficients).1 ∧
        e.stacks 195=[] ∧ e.stacks 204=depth ∧
        (∀ i, (¬ ∃ j, search j=i) → e.stacks i=a.stacks i) := by
  obtain ⟨n,hn,raw,hsearch,hraw,hready,h25,hwidth⟩ := searchCall_eval a depth hd ha
  let a1 := embedState (registers 22 (by decide)) search a raw
  have h202 : a1.stacks 202=a.stacks 202 := by
    exact embedState_stack_frame _ _ _ _ _ (by decide)
  have hs639 : a1.stacks 639=[] := by
    rw [show a1.stacks 639=a.stacks 639 from
      embedState_stack_frame _ _ _ _ _ (by decide)]
    exact h639
  have h432 : a1.stacks 432=raw.stacks 12 :=
    embedState_stack _ _ _ _ search_injective 12
  let a2 : Data := ⟨readRegs a1.regs 30 31 none,
    Function.update a1.stacks 432 (a1.stacks 202)⟩
  have hc : Eval (overwrite 202 432)
      (2*(a1.stacks 432).length+7*(a1.stacks 202).length+8) a1 a2 :=
    overwrite_eval 202 432 a1 (by decide) (by decide) (by decide) hs639
  have hlocal : (projectState (registers 22 (by decide)) search a2).stacks =
      Function.update raw.stacks 12 (a.stacks 202) := by
    funext i
    change Function.update a1.stacks 432 (a1.stacks 202) (search i)=_
    by_cases hi : i=12
    · subst i
      simpa [search] using h202
    · have hne : search i≠432 := by
        intro h
        exact hi (search_injective h)
      rw [Function.update_of_ne hne,Function.update_of_ne hi]
      exact embedState_stack _ _ _ _ search_injective i
  have hlocalState : projectState (registers 22 (by decide)) search a2 =
      ⟨(projectState (registers 22 (by decide)) search a2).regs,
        Function.update raw.stacks 12 (a.stacks 202)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk rfl hlocal
  have hr : RingCoefficientLiftProgram.SearchReady
      (projectState (registers 22 (by decide)) search a2) := by
    rw [hlocalState]
    exact search_padding_ready depth raw hready h25 _ _
  have hi : a2.stacks 195=IrreducibleSearchProgram.coefficientArray
      (List.ofFn (IrreducibleSearch.data hd).coefficients) := by
    have hh := congrFun hlocal (13 : Fin 28)
    simpa [projectState,search,hraw] using hh
  have hw2 : (a2.stacks 432).length=baseWidth 3 t := by
    simpa [a2,h202] using hw
  obtain ⟨e,hpad,he⟩ := paddingCall_eval a2 t ht depth.length hd hr hi hw2
  refine ⟨n+(2*(a1.stacks 432).length+7*(a1.stacks 202).length+8)+
    (depth.length*(28*t+14)+7),?_,e,?_,?_,?_,?_,?_⟩
  · rw [h432,h202,hw]
    omega
  · simpa only [searchAndPad,Nat.add_assoc] using hsearch.seq (hc.seq hpad)
  · simp only [he,Function.update_same]
  · simp [he]
  · have h204 : a1.stacks 204=raw.stacks 14 :=
      embedState_stack _ _ _ _ search_injective 14
    simpa [he,a2,h204] using hready.controls.1
  · intro i hi
    have hi195 : i≠195 := by intro h; subst i; exact hi ⟨13,rfl⟩
    have hi441 : i≠441 := by intro h; subst i; exact hi ⟨21,rfl⟩
    have hi432 : i≠432 := by intro h; subst i; exact hi ⟨12,rfl⟩
    simp only [he,Function.update_of_ne hi441,Function.update_of_ne hi195,a2,
      Function.update_of_ne hi432]
    exact embedState_stack_frame _ _ _ _ _ hi

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram



namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing StackRoutines

structure CoreOutput (t d : ℕ) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) (a : Data) : Prop where
  modulus : a.stacks 194=M.bits
  width : (a.stacks 202).length=baseWidth 3 t
  degree : (a.stacks 204).length=d
  zero : a.stacks 203=cache.zero.val
  one : a.stacks 498=cache.one.val
  minusOne : a.stacks 508=cache.minusOne.val
  half : a.stacks 253=u.val
  precision : a.stacks 212=List.replicate t true
  inverse : (2 : ZMod (3^t))*wordValue 3 t u=1
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  oneCanonical : BinaryArithmetic.toNat cache.one.val < 3^t
  table : a.stacks 201=RingProgramTable.modelTable t model M cache

/-- This core result has no modulus, irreducible polynomial, scalar cache,
or table premise.  All four objects are generated by the executed code. -/
theorem CoreOutput.reindex {t d D : ℕ} (heq : d=D) (hd : 0 < d) (hD : 0 < D)
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {u : RingProgram.ScalarCode 3 t} {a : Data}
    (h : CoreOutput t d (IrreducibleSearch.data hd) M cache u a) :
    CoreOutput t D (IrreducibleSearch.data hD) M cache u a := by
  cases heq
  exact h

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls StackRoutines

theorem copyPlan_eval (ps : List (Fin 640 × Fin 640)) (a : Data)
    (hports : ∀ p∈ps,p.1≠p.2 ∧ p.1≠639 ∧ p.2≠639)
    (hwork : a.stacks 639=[]) :
    Eval (copyPlan ps) (copyPlanCost ps a) a (copiedPlan ps a) := by
  induction ps generalizing a with
  | nil => exact .base (.skip _)
  | cons p ps ih =>
    have hp := hports p (by simp)
    have he := overwrite_eval p.1 p.2 a hp.1 hp.2.1 (Ne.symm hp.2.2) hwork
    have ht := ih (copied p a) (fun q hq => hports q (by simp [hq]))
      (by simpa [copied,hp.2.2,Ne.symm hp.2.2] using hwork)
    exact he.seq ht

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing

/-- The node generator reads only its scalar-width zero word, binary count,
and unary dimension.  All other global metadata remains framed. -/
theorem nodesCall_produces (t : ℕ) (ht : 0 < t) (a : Data) (h : NodesInput t a) :
    ∃ n ≤ RingNodeProgram.budget (baseWidth 3 t) (a.stacks 625).length
        (a.stacks 204).length (BinaryArithmetic.toNat (a.stacks 625))+5,
      ∃ e : Data, Eval nodesCall n a e ∧
        e.stacks 256=((nodeWords t (a.stacks 204).length
          (BinaryArithmetic.toNat (a.stacks 625))).map RingProgram.flat).flatten ∧
        e.stacks 204=a.stacks 204 ∧
        (∀ i, (¬∃ j,nodes j=i) → e.stacks i=a.stacks i) := by
  let r := a.regs ∘ registers 8 (by decide)
  have hi : projectState (registers 8 (by decide)) nodes a =
      SubexpFieldRowPreparation.data r (List.replicate (baseWidth 3 t) false)
        (a.stacks 625) (a.stacks 204) [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · exact h.clean 0 (by decide)
    · exact h.clean 1 (by decide)
    · exact h.clean 2 (by decide)
    · exact h.clean 3 (by decide)
    · exact h.clean 4 (by decide)
    · exact h.zero
    · exact h.clean 6 (by decide)
    · exact h.clean 7 (by decide)
    · exact h.clean 8 (by decide)
    · exact h.clean 9 (by decide)
    · exact h.clean 10 (by decide)
    · exact h.clean 11 (by decide)
    · exact h.clean 12 (by decide)
    · rfl
    · rfl
  obtain ⟨n,hn,rf,last,he,hv,hl⟩ := nodesCall_eval a r t ht (a.stacks 625) (a.stacks 204) hi
  refine ⟨n,hn,_,he,?_,?_,?_⟩
  · exact embedState_stack _ _ _ _ nodes_injective 12
  · exact embedState_stack _ _ _ _ nodes_injective 14
  · intro i hi
    exact embedState_stack_frame _ _ _ _ _ hi

/-- The length used by all node-stream copies follows from the actually
constructed fixed-width words. -/
theorem nodeWords_flat_length (t d Q : ℕ) :
    (((nodeWords t d Q).map RingProgram.flat).flatten).length=Q*(d*baseWidth 3 t) := by
  rw [LeafProgram.NodeFrames.flatten_length (d*baseWidth 3 t)
    ((nodeWords t d Q).map RingProgram.flat) (by
      intro word hw
      obtain ⟨code,hcode,rfl⟩ := List.mem_map.mp hw
      exact RingProgram.flat_length code)]
  simp

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

abbrev constantsPhase : Cmd 32 640 :=
  .seq (clearPorts constantStartPorts) (.seq constantBatch (copyPlan constantAliases))

theorem constantsPhase_eval (a : Data) {B : ℕ} (one minusOne zero : Word B)
    (W : ℕ) (hw : ∀ i,(a.stacks i).length ≤ W)
    (h1 : a.stacks 498=one.val) (hm : a.stacks 508=minusOne.val)
    (hz : a.stacks 203=zero.val) :
    ∃ n ≤ constantsBudget W B (a.stacks 204).length, ∃ e : Data,
      Eval constantsPhase n a e ∧ e.stacks=constantResultStacks a one minusOne zero := by
  let a0 := clearedPorts constantStartPorts a
  have hc := clearPorts_eval constantStartPorts a
  have hframe (i : Fin 640) (hi : i∉constantStartPorts) : a0.stacks i=a.stacks i := by
    simp only [a0,clearedPorts_stacks,hi,ite_false]
  obtain ⟨nb,hnb,a1,hb,hsb⟩ := constantBatch_eval a0 one minusOne zero
    (by simpa only [hframe 498 (by decide)] using h1)
    (by simpa only [hframe 508 (by decide)] using hm)
    (by simpa only [hframe 203 (by decide)] using hz)
    (by simp [a0,clearedPorts_stacks,constantStartPorts])
    (by simp [a0,clearedPorts_stacks,constantStartPorts])
    (by
      intro out hout i hi
      simp only [a0,clearedPorts_stacks]
      have hm' : constant out i∈constantStartPorts := by
        simp only [constantStartPorts,List.mem_append,List.mem_flatMap]
        exact Or.inr ⟨out,hout,List.mem_map_of_mem hi⟩
      simp [hm'])
  have h639 : a1.stacks 639=[] := by
    rw [hsb]
    simp [constantBatchStacks,a0,clearedPorts_stacks,constantStartPorts]
  have hp := copyPlan_eval constantAliases a1 (by
    intro p hp
    simp only [constantAliases,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> decide) h639
  let cb := constantStartPorts.length*(2*W+3)
  let bb := 3*(7*B+8+(LeafProgram.Constants.budget B (a.stacks 204).length+1))
  have hnc : clearPortsCost constantStartPorts a ≤ cb :=
    clearPortsCost_bound constantStartPorts a W (fun i _ => hw i)
  have hnb' : nb ≤ bb := by simpa [bb,hframe 204 (by decide)] using hnb
  have hwidth : ∀ i,(a1.stacks i).length ≤ W+(cb+bb)+2 := by
    intro i
    have h := eval_width_le (hc.seq hb) hw i
    omega
  have hpc := copyPlanCost_bound constantAliases a1 (W+(cb+bb)+2) hwidth
  refine ⟨clearPortsCost constantStartPorts a+nb+copyPlanCost constantAliases a1,
    ?_,copiedPlan constantAliases a1,?_,?_⟩
  · change _ ≤ cb+bb+constantAliases.length*(9*(W+(cb+bb)+2)+8)
    omega
  · simpa only [constantsPhase,Nat.add_assoc] using hc.seq (hb.seq hp)
  · simp only [constantResultStacks]
    have hst : a1.stacks=(⟨a0.regs,constantBatchStacks a0 one minusOne zero⟩ : Data).stacks := hsb
    simp only [constantAliases,copiedPlan,copied,hst,a0]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing StackRoutines

abbrev nodesPhase : Cmd 32 640 :=
  .seq (clearPorts nodesStartPorts) (.seq (copyPlan nodeInputs) (.seq nodesCall
    (.seq (overwrite 256 628) (.seq nodeFramesCall (overwrite 628 256)))))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

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

def Query.Valid (q : Query) : Prop :=
  0 < q.width.length ∧ 0 < BinaryArithmetic.toNat q.ambient ∧
  (∀ i, q.clauses[i.val]=Encoding.encodeList Encoding.encodeNat (q.codes i)) ∧
  3*q.clauses.length ≤ 2^q.width.length ∧
  (∀ i, q.mark=some i → q.index=Encoding.encodeNat i.val) ∧
  BinaryArithmetic.toNat q.modulus=q.clauses.length ∧
  (∀ row ∈ q.scopeRows, ∀ v ∈ row, v < BinaryArithmetic.toNat q.ambient)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

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

def BankEmpty (a : Local) : Prop := ∀ i,a.stacks (ports i)=[]

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedFactorBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The factor specification uses the actual generated idempotent code and
native node word. The existential scalar preparation of the code is retained
as a witness; no canonical-byte assumption is needed. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

structure GeneratedCode (t : ℕ) (bits : List Bool) where
  modulus : SubexpPreparedQuartic.Modulus 3 t
  cache : RingProgram.ScalarCache 3 t
  half : RingProgram.ScalarCode 3 t
  bytes : bits=RingProgram.flat (IdempotentProgram.binaryLiftWords t modulus cache half)
  inverse : (2 : ZMod (3^t))*wordValue 3 t half=1

def GeneratedCode.code {t : ℕ} {bits : List Bool} (g : GeneratedCode t bits) :=
  IdempotentProgram.binaryLiftWords t g.modulus g.cache g.half

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCoreBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.numericCost (q : Query) (k : ℕ) : ℕ :=
  LeafQueryFrontend.numericCost q.ambient q.modulus k (totals q.scopeRows q.forward).free
    (totals q.scopeRows q.forward).occurrence (completedArity q.scopeRows q.forward)
    (q.scopeRows.length+(totals q.scopeRows q.forward).uncovered)
    (totals q.scopeRows q.forward).incidences

def Query.inputLengths (q : Query) (k : ℕ) : Fin 8 → ℕ := fun _ => q.numericCost k

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The ring producer can clear low arithmetic workspace, but never inserts
data there.  Thus initially blank low node-work tapes stay blank.  This is a
property of the existing program, not an additional cleanup operation. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame
open BitProgram StructuredCalls

theorem copyPlan (ps : List (Fin 640 × Fin 640)) (i : Fin 640) (hi : i.val < 190)
    (hp : ∀ p∈ps,190 ≤ p.1.val ∧ 190 ≤ p.2.val) :
    EmptyPreserved (LeafRingSetupProgram.copyPlan ps) i := by
  induction ps with
  | nil => exact skip i
  | cons p ps ih =>
    exact seq (overwrite p.1 p.2 i hi (hp p (by simp)).1 (hp p (by simp)).2)
      (ih (fun q hq => hp q (by simp [hq])))

theorem constants (i : Fin 640) (hi : i.val < 190) : EmptyPreserved constantsPhase i :=
  seq (clearPorts _ i) (seq
    (seq (buildConstant 498 207 i hi (by decide) (by decide))
      (seq (buildConstant 508 211 i hi (by decide) (by decide))
        (buildConstant 203 280 i hi (by decide) (by decide))))
    (copyPlan constantAliases i hi (by
      intro p hp
      simp only [constantAliases,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl <;> decide)))

theorem nodes (i : Fin 640) (hi : i.val < 190) : EmptyPreserved nodesPhase i := by
  have hn : EmptyPreserved nodesCall i := by
    apply highLift _ _ _ i hi
    intro j
    unfold LeafRingSetupProgram.nodes
    split_ifs <;> (try dsimp only) <;> omega
  have hf : EmptyPreserved nodeFramesCall i := by
    apply highLift _ _ _ i hi
    intro j
    fin_cases j <;> decide
  exact seq (clearPorts _ i) (seq (copyPlan nodeInputs i hi (by
      intro p hp
      simp only [nodeInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> decide))
    (seq hn (seq (overwrite 256 628 i hi (by decide) (by decide))
      (seq hf (overwrite 628 256 i hi (by decide) (by decide))))))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
end


