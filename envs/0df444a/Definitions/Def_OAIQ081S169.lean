-- Prove2me | Definitions.Def_OAIQ081S169
-- name    : OAIQ081S169
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:15:22.478989+00:00
-- url     : https://prove2.me/theorems/5d1ac625-6d6d-4487-8b46-f86f538cf163
-- title:
--   Definitions bundle OAIQ081S169 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 74 declarations of OpenAI's Lean: 50 definitions, 3 inductive types or structures and 21 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.parameters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache.unaryRuntime`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth.code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cacheCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepareCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.unaryValues`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.CountsBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.height`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.postMajorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.preHeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.widthHeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds.widthInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.finalModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.intervalModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete.weightedHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.clauses`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.ctx`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.digits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.markedClause`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.Spec.rawRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.sourceContext`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.binaryDigits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.decodedHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.pulled`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.sourceHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.universal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.arithmeticBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Source.nativeOutputBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.BankFields`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Exported` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_QueryProgram`, `SubexponentialSAT_SqrtLog_LeafOuterProgramBase`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBanked`, `SubexponentialSAT_SqrtLog_LeafParametersProgramCache`, `SubexponentialSAT_SqrtLog_LeafParametersProgramCacheWidth`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExports`, `SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds`, `SubexponentialSAT_SqrtLog_LeafParametersProgramInterval`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcrete`, `SubexponentialSAT_SqrtLog_LeafProgramFactorInput`, `SubexponentialSAT_SqrtLog_LeafProgramFactorSpec`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteCode`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteLocality`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteRows`, `SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteSpecTarget`, `SubexponentialSAT_SqrtLog_LeafProgramPreparedSpec`, `SubexponentialSAT_SqrtLog_LeafProgramQueryArithmetic`, `SubexponentialSAT_SqrtLog_LeafProgramQueryRing`, `SubexponentialSAT_SqrtLog_LeafProgramSourceNativeCost`, `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyBank`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendHighRun`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendPost`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramLowFrame`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative`, `SubexponentialSAT_SqrtLog_PackingCallerProgramState`, `SubexponentialSAT_SqrtLog_RingProgramTableBridge`, `SubexponentialSAT_SqrtLog_RingProgramTableCanonical`, `SubexponentialSAT_SqrtLog_RingProgramTableMachine`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S153`, `OAIQ081S155`, `OAIQ081S157`, `OAIQ081S158`, `OAIQ081S159`, `OAIQ081S162` and `OAIQ081S163` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S173`, `OAIQ081S174`, `OAIQ081S175`, `OAIQ081S176`, `OAIQ081S177`, `OAIQ081S178` and `OAIQ081S179`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.shifted_source_typed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cacheCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_length`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization.uniform_guarded_lengths_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.earlyCall_eval_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace.staged_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.overlay_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.advance_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.shifted_source_typed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.cacheCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_binary_length`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.prepared_unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.earlyCall_eval_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCommand_eval_bounded` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.program_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S155
import Definitions.Def_OAIQ081S157
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S159
import Definitions.Def_OAIQ081S162
import Definitions.Def_OAIQ081S163

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end finite readout machine. Runtime words supply both loop counts,
the ambient shape, and the already constructed coefficient zero vector. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def command : WideCode := .seq prepare (.seq outer finish)
def program := compiled command 15 0

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def stageCost (a : OuterData) : ℕ :=
  LeafProgram.Incidence.stageCost (projectState id basePort (initialized a)) + 1

def exportCost (a : OuterData) : ℕ :=
  LeafProgram.Incidence.exportCost (projectState id basePort a) + 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

open StructuredCalls

@[simp] theorem pairCallResult_stack_frame (d : State 40 896) (i : Fin 896)
    (hi : i ≠ 848) : (pairCallResult d).stacks i = d.stacks i := by
  simp [pairCallResult, hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

abbrev command : Cmd 8 77 := Circuit.program code

theorem values (m : Model) :
    (result code m).val 44=m.val 35-2 ∧ (result code m).val 45=2*m.val 33 := by
  simp [code,result,next,value,output]
  omega

theorem frame (m : Model) (a : Fin 64) (h44 : a≠44) (h45 : a≠45) :
    (result code m).val a=m.val a := by
  simp [code,result,next,value,output,h44,h45]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared fixed port maps and the paid native code-parameter stage. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

abbrev parameters : Cmd 40 896 :=
  stage parameterInputs CodeParametersProgram.program regs8 stacks77 parameterOutputs


end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBanked
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

theorem guard_code_preserves_input (i : Fin 8) :
    ∀ j ∈ GuardSetup.code, Circuit.output j ≠ i.castAdd 56 := by
  fin_cases i <;> decide

theorem guardedModel_input (x : Input) (l : Fin 8 → ℕ) (i : Fin 8) :
    (guardedModel x l).val (i.castAdd 56)=Layout.initialValues x (i.castAdd 56) := by
  have hi : (i.castAdd 56).val < 44 := by have := i.isLt; simpa using (show i.val < 44 by omega)
  change (if (i.castAdd 56).val < 44 then (Prepared.finalModel x l).val (i.castAdd 56) else 0)=_
  rw [ite_eq_left hi]
  calc
    _ = (Layout.model x l).val (i.castAdd 56) := by
      exact result_value_frame GuardSetup.code (Layout.model x l) _
        (guard_code_preserves_input i)
    _ = _ := Layout.model_inputs x l i

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCacheWidth
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid binary metadata for the integer entry cache. The centered interval
start on port46 is produced by `SubexpIntervalStartProgram.program`; its
semantic identification is `SubexpIntervalStart.value_eq_intervalStart`.
This stage preserves that word and the parameter table while forming Qr and
the sufficient scalar width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Inputs r18, Q21, R29 and A46. Outputs Qr47 and cache width50;
48 and49 are paid temporary product words. -/
def code : List Instr := [
  .clear 47, .mul 21 18 47 (by decide) (by decide),
  .clear 48, .mul 46 29 48 (by decide) (by decide),
  .clear 49, .add 48 48 49 (by decide) (by decide),
  .clear 50, .add 49 21 50 (by decide) (by decide), .addConst 50 1]

abbrev command : Cmd 8 77 := Circuit.program code

end SubexponentialSAT.SqrtLog.LeafParametersProgram.CacheWidth

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramInterval
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

def prepare : List Instr := [
  .clear 46,.clear 47,.clear 48,.clear 49,.clear 50,.clear 51,
  .clear 52,.clear 53,.clear 54,.clear 55,.clear 56,.clear 57,
  .clear 58,.clear 59,.clear 60,.clear 61,.clear 62,.clear 63]

def intervalModel (m : Model) : Model :=
  let p := result prepare m
  { val := Function.update p.val 46
      (Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29))
    len := Function.update p.len 46 (4*(m.len 18+m.len 21+m.len 29+1)) }

abbrev command : Cmd 8 77 :=
  .seq (Circuit.program prepare) (.seq intervalAt CacheWidth.command)

def finalModel (m : Model) : Model := result CacheWidth.code (intervalModel m)

def runtimeBound (m : Model) : ℕ :=
  budget prepare m+10000*(m.len 18+m.len 21+m.len 29+1)^2+1+
    budget CacheWidth.code (intervalModel m)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

def unaryRuntime (m : Model) : ℕ :=
  unaryBound (m.val 29) (m.len 29)+unaryBound (m.val 46) (m.len 46)+
    unaryBound (m.val 50) (m.len 50)

abbrev command : Cmd 8 77 := .seq Interval.command unaryCommand
def runtimeBound (m : Model) : ℕ :=
  Interval.runtimeBound m+unaryRuntime (Interval.finalModel m)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Cache

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

def cacheCall : Code := liftCommand Cache.command (Bank.port 18) (Bank.port 53) bankRegs bank

def prepareCommand : Code := .seq cacheCall (.seq exportCommand clearCommand)

def unaryValues (m : Model) : Fin 8 → ℕ :=
  ![m.val 0,m.val 5,m.val 18,m.val 21,m.val 21*m.val 18,m.val 29,
    Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29),
    1+2*Subexp.TailInterval.intervalStart (m.val 18) (m.val 21) (m.val 29)*m.val 29+m.val 21]

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual parameter/export prefix. Only
input counts and input word lengths enter the final bound. In particular the
large grid value never becomes a unary counter in this prefix. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod



def preHeight (B : ℕ) := iterMajorant Interval.prepare.length (B+2)
def widthInput (B : ℕ) := preHeight B+16*(B+1)
def widthHeight (B : ℕ) := iterMajorant CacheWidth.code.length (widthInput B)
def height (B : ℕ) := preHeight B+widthHeight B+valueHeight B+B+1

/-- A concrete fixed polynomial majorant expressed using two fixed iterates
of the already certified arithmetic-table majorant. -/
def postMajorant (B : ℕ) : ℕ := 200000*(height B)^2

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramFrontendInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input-only closure of the physical parameter/cache/export costs, including
the exact binary word lengths used by the subsequent offset producer. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds
open BinaryArithmetic Bank Circuit Asymptotic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def CountsBound (x : Input) (S : ℕ) : Prop :=
  ∀ i : Fin 8,Layout.initialValues x (i.castAdd 56) ≤ S

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.FrontendBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Derivation of the source-bank invariant from its paid master copies.
The source numerator sees empty 5/10 only inside the checked staging wrapper. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

structure BankFields {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (s : Fin 320 → List Bool) : Prop where
  colors : s 21=List.replicate r true
  nodes : s 22=List.replicate Q true
  index : s 25=[true]
  typeWidth : s 26=List.replicate (Q*r) true
  positive : s 42=p.saved.hp
  negative : s 43=p.saved.hn
  scalarWidth : s 44=p.width
  power : s 45=p.power.1
  radius : s 47=List.replicate p.R true
  offset : s 48=p.aWord
  zeroCache : s 249=RingProgram.flat p.ops.zeroRun.1
  oneCache : s 250=RingProgram.flat p.ops.oneRun.1
  minusCache : s 251=RingProgram.flat p.minusOne
  inverseDenominator : s 252=RingProgram.flat p.invDenom
  inverses : s 308=(List.ofFn (fun i => RingProgram.flat (p.inverse i))).flatten
  negatives : s 309=(List.ofFn (fun i => RingProgram.flat (p.negative i))).flatten
  differences : s 310=(List.ofFn (fun i => (List.ofFn (fun j => RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : s 311=p.ringWidth
  rowWidth : s 312=p.rowWidth
  zero : s 313=RingProgram.flat p.ops.zeroRun.1
  one : s 314=RingProgram.flat p.ops.oneRun.1

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceNativeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A uniform cost for the actual source invocation, including its global
staging, four-cache save/restore, and cleanup. The size assumption includes the
live incidence-table accumulator rather than quantifying over unbounded data. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpSetupStorage
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

def nativeOutputBound {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (N S : ℕ) : ℕ :=
  67108864*S+1+(p.R+1)*(d*baseWidth 3 p.t)+(p.R+1)+
    N*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

noncomputable def sourceContext {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n u J : ℕ) (width : List Bool) (hw : width.length=baseWidth 3 p.t) : Context 3 p.t n d :=
  ⟨p.modulus,p.cache,p.hz,HornerProgram.modelTable p.t p.model p.modulus p.cache,u,J,width,hw⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorSpec
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source data and physical premises for the concrete factor callback.
The records below contain no execution hypotheses. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram NativeSemantics SubexpSetupStorage

structure Spec (r Q n d : ℕ) where
  p : SourceBank.Parameters r Q d
  ps : List (ℕ × ℕ)
  packing : PackingData (Fin ps.length) (UniversalType r Q 1)
  u : ℕ
  J : ℕ
  hu : 0 < u
  hJ : 0 < J
  theta : Coeff (baseWidth 3 p.t) d
  width : List Bool
  widthLength : width.length=baseWidth 3 p.t
  minus : RingProgram.Code (Word (baseWidth 3 p.t)) d
  minusValue : p.ops.decode minus = -1
  one : Raw (p:=3) (t:=p.t) (n:=n) (d:=d)
  oneGood : Good Finset.univ u J one
  oneValue : rawDenote p.ops.decode one=Squarefree.canonical u J 1
  source : List (List (SAT.Literal (Fin n)))
  rows : List (List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
  bitWidth : ℕ
  bitWidthPositive : 0 < bitWidth
  sourceBound : 3*(HashInputProgram.Expansion.encodedClauses source).length ≤ 2^bitWidth
  code : RingProgram.Code (RingProgram.ScalarCode 3 p.t) (3*p.t)
  marked : Bool
  mark : ℕ
  markValid : marked=true → mark < source.length

namespace Spec
variable {r Q n d : ℕ} (q : Spec r Q n d)
noncomputable def ctx : Context 3 q.p.t n d := sourceContext q.p n q.u q.J q.width q.widthLength

def rawRows : List (List Bool) := q.rows.map fun ts=>(HashInputProgram.Loop.rawInput q.bitWidth ts).reverse
def clauses : List (List Bool) := HashInputProgram.Expansion.encodedClauses q.source
def markedClause : List (SAT.Literal (Fin n)) := q.source[q.mark]?.getD []
def digits := List.ofFn (IdempotentApplyProgram.coefficientTriple q.p.t q.code)
end Spec

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramAssignmentConcrete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The relational, actually executed assignment fold has the same value as
the selected-factor expression used by the node proof.  This bridge chooses
no raw representative and retains the shared U and T truncations. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open HashCircuitProgram HashCircuitProgram.Native
open scoped BigOperators

variable {r Q n d : ℕ}

def weightedHashes (q : Factor.Spec r Q n d) :
    List (List (Row.WeightedClause n (baseWidth 3 q.p.t) d)) :=
  q.rows.map (HashInputProgram.Expansion.weightedRow q.p.t d q.source)

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source rows used by the native factor callback retain their concrete
origin, degree, and original-coordinate support after incidence pullback. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly

variable {r Q d : ℕ}

abbrev universal (p : SourceBank.Parameters r Q d) :=
  LayoutUniversal.data (r:=r) p.aWord.length p.R p.denom p.hdenom
    (p.model.nodeUnits p.t Q p.ht p.hfield)

abbrev copied (p : SourceBank.Parameters r Q d) {D : ℕ}
    (P : PackingData (Fin D) (UniversalType r Q 1)) :=
  LayoutBlocks.data (universal p) P.completeBlocks id
    (fun i => (universal p).color (P.label i)) (fun _ _ => rfl)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The target uses the actual binary Newton coefficient array. Its constant
and degree statements do not replace it by a separate coefficient algorithm. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly

variable {r Q d n : ℕ}

def binaryDigits (p : SourceBank.Parameters r Q d)
    (M : SubexpPreparedQuartic.Modulus 3 p.t) (cache : RingProgram.ScalarCache 3 p.t)
    (half : RingProgram.ScalarCode 3 p.t) : Fin p.t → Polynomial (p.model.O p.t) :=
  fun s => (IdempotentProgram.digitPolynomial (RingProgram.scalarRing 3 p.t M cache)
    (IdempotentProgram.binaryLiftWords p.t M cache half) s).map (p.model.base p.t)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality of the integer signatures emitted by the actual matrix implies
exact equality of the source-row baseline in the full coefficient ring. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutExactBuckets LayoutPullback

variable {r Q d D n : ℕ}

abbrev pulled (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i)) :=
  LayoutHeadPullback.pullback owner id head (copied p P) (fun t i=>hhead i t)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteSpecTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One source target is attached to the concrete factor specification. It
retains raw term multiplicity, optional marked violation, and shared U order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native

variable {r Q d n : ℕ}

def sourceHashes (q : Factor.Spec r Q n d) : List (SparseRow (Fin n) (ZMod 3)) :=
  q.rows.map (fun terms=>terms.map (fun term=>(term.2,HashInputProgram.Expansion.originalClause q.source term.1)))

def decodedHashes (q : Factor.Spec r Q n d) : List (SparseRow (Fin n) (q.p.model.O q.p.t)) :=
  (AssignmentConcrete.weightedHashes q).map (NativeSemantics.sourceTerms q.p.ops.decode)

@[simp] theorem sourceHashes_length (q : Factor.Spec r Q n d) :
    (sourceHashes q).length=q.rows.length := by simp [sourceHashes]

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t)

theorem powerData_eq_callback {d : ℕ} (hd : 0 < d)
    (c : List.Vector (Word (baseWidth p t)) d)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (ho : BinaryArithmetic.toNat cache.one.val < p^t)
    (n : ℕ) (i : Fin d) :
    (iterData p t M cache.zero cache.minusOne c n (initialData d cache.one cache.zero)).coefficients.get i =
      (RingProgram.powerVectorRun (RingProgram.scalarProgram p t M cache) c.get n).1 i := by
  apply RingProgram.word_eq_of_value p t
  · exact powerData_canonical p t M cache c hz ho n i
  · exact callbackPower_canonical p t M cache c.get hz ho n i
  · have h := congrFun (powerData_decode p t M hd cache.one cache.zero cache.minusOne
      cache.one_correct cache.zero_correct cache.minusOne_correct c n) i
    have h' := congrFun (RingProgram.powerVectorRun_correct
      (RingProgram.scalarRing p t M cache) c.get n) i
    exact h.trans h'.symm

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

open SubexponentialSAT.BinaryArithmetic in
theorem nativeTable_eq_callback (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (hd : 0 < d) (c : List.Vector (Word (baseWidth p t)) d)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) (ho : BinaryArithmetic.toNat cache.one.val < p^t) :
    RingTriple.tableEncoding (fun i j k =>
      (iterData p t M cache.zero cache.minusOne c (i.val+j.val)
        (initialData d cache.one cache.zero)).coefficients.get k) =
      RingTriple.tableEncoding (RingProgram.structureTableRun
        (RingProgram.scalarProgram p t M cache) c.get).1 := by
  congr 1
  funext i j k
  simpa only [RingProgram.structureTableRun, List.Vector.get_ofFn] using
    powerData_eq_callback p t M cache hd c hz ho (i.val+j.val) k

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable.Machine

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (hd : 0 < d) (c : List.Vector (Word (baseWidth p t)) d)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t)
    (ho : SubexponentialSAT.BinaryArithmetic.toNat cache.one.val < p^t)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ n ≤ preparationBudget (baseWidth p t) d + RingTableLayout.budget d (baseWidth p t)+2,
      ∃ rf, Eval command n
      (state regs (initialStore s c cache.one cache.zero cache.minusOne) [])
      (state rf (ready {s with powers := allPowerBits p t M c cache.one cache.zero cache.minusOne, rounds := []}
        c (iterData p t M cache.zero cache.minusOne c (2*d-2) (initialData d cache.one cache.zero)) cache.zero cache.minusOne)
        (RingTriple.tableEncoding (RingProgram.structureTableRun
          (RingProgram.scalarProgram p t M cache) c.get).1)) := by
  obtain ⟨ri,ni,hni,ht⟩ := RingProgramTable.program_run p t M hd c cache.one cache.zero cache.minusOne s regs hmod hw hdegree
  let final := ready {s with powers := allPowerBits p t M c cache.one cache.zero cache.minusOne, rounds := []}
    c (iterData p t M cache.zero cache.minusOne c (2*d-2) (initialData d cache.one cache.zero)) cache.zero cache.minusOne
  have he := eval_call_lifted RingProgramTable.program id prepPorts
    (state regs (initialStore s c cache.one cache.zero cache.minusOne) [])
    Function.injective_id prepPorts_injective ht
  have he' : Eval prep ni (state regs (initialStore s c cache.one cache.zero cache.minusOne) [])
      (state ri final []) := by
    simpa only [prep, embed_prep, final] using he
  let P := fun j => (iterData p t M cache.zero cache.minusOne c j (initialData d cache.one cache.zero)).coefficients.get
  obtain ⟨nl,hnl,rf,hl⟩ := layout_eval P final ri
    (allPowerBits_eq_powerRecords p t M hd c cache.one cache.zero cache.minusOne) hdegree hw
  rw [nativeTable_eq_callback p t M cache hd c hz ho] at hl
  exact ⟨ni+nl, by omega, rf, he'.seq hl⟩


theorem program_run (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (hd : 0 < d) (c : List.Vector (Word (baseWidth p t)) d)
    (hz : SubexponentialSAT.BinaryArithmetic.toNat cache.zero.val < p^t)
    (ho : SubexponentialSAT.BinaryArithmetic.toNat cache.one.val < p^t)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ rf, RunsIn program
      (preparationBudget (baseWidth p t) d + RingTableLayout.budget d (baseWidth p t)+3)
      ((state regs (initialStore s c cache.one cache.zero cache.minusOne) []).withPC (some program.entry))
      ((state rf (ready {s with powers := allPowerBits p t M c cache.one cache.zero cache.minusOne, rounds := []}
        c (iterData p t M cache.zero cache.minusOne c (2*d-2) (initialData d cache.one cache.zero)) cache.zero cache.minusOne)
        (RingTriple.tableEncoding (RingProgram.structureTableRun
          (RingProgram.scalarProgram p t M cache) c.get).1)).withPC none) := by
  obtain ⟨n,hn,rf,he⟩ := command_eval p t M cache hd c hz ho s regs hmod hw hdegree
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 27 0⟩

end SubexponentialSAT.SqrtLog.RingProgramTable.Machine

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
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpQuarticRing
open IdempotentPreparationProgram

abbrev scalarCommand : Cmd 8 41 := .seq boot Scalar.command

abbrev scalarCall : Cmd 32 640 :=
  liftCommand scalarCommand 31 17 (registers 8 (by decide)) scalar

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/- Component: LeafRingSetupProgramSearch.lean -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open RingProgramTable

attribute [local instance] OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.instFactPrimeOfNatNat_solutions_1
theorem table_program_run (t : ℕ) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (ho : BinaryArithmetic.toNat cache.one.val < 3^t)
    (s : Store) (regs : Fin 8 → Bool) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth 3 t) (hdegree : s.degree.length = d) :
    ∃ rf, RunsIn Machine.program (208000*(d+1)^5*(t+1)^2)
      ((Machine.state regs
        (initialStore s (modelCoefficients t a) cache.one cache.zero cache.minusOne) []).withPC
        (some Machine.program.entry))
      ((Machine.state rf (preparedStore 3 t M cache (modelCoefficients t a) s)
        (modelTable t a M cache)).withPC none) := by
  let c := modelCoefficients t a
  obtain ⟨rf, n, hn, he⟩ := Machine.program_run 3 t M cache hd c hz ho s regs
    hmod hw hdegree
  refine ⟨rf, n, ?_, ?_⟩
  · apply hn.trans
    apply (Machine.nativeBudget_polynomial (baseWidth 3 t) d).trans
    rw [RingProgram.ternary_baseWidth]
    have h : (2*t+1)^2 ≤ 4*(t+1)^2 := by
      calc
        (2*t+1)^2 ≤ (2*(t+1))^2 := Nat.pow_le_pow_left (show 2*t+1 ≤ 2*(t+1) by omega) 2
        _ = _ := by ring
    nlinarith [Nat.mul_le_mul_left (52000*(d+1)^5) h]
  · simpa only [preparedStore, modelTable, c, modelCoefficients_get] using he

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramNodes.lean -/

/-! Physical node generation and record framing at the ring-setup ports. -/

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
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls

abbrev serializationCall : Cmd 32 640 :=
  liftCommand LeafParametersProgram.Serialization.command 33 44
    (registers 8 (by decide)) parameters


end SubexponentialSAT.SqrtLog.LeafRingSetupProgram


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/



namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing StackRoutines

/-- The arithmetic core uses the generated scalar cache, searches for the
extension polynomial, and constructs its multiplication table. -/
abbrev coreCommand : Cmd 32 640 :=
  .seq scalarCall (.seq (overwrite 507 253) (.seq RegisterResetProgram.all
    (.seq searchAndPad (.seq (overwrite 498 538) tableCall))))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls StackRoutines LeafParametersProgram

/-- The prelude_ preserves the numerical bank until the last dependent
counter and node-count word have been consumed. -/
abbrev numberPhase : Cmd 32 640 :=
  .seq (clearPorts (workPorts++outputPorts))
    (.seq serializationCall (.seq (unaryPlan numericPlan)
      (.seq (overwrite 373 511) RegisterResetProgram.all)))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing StackRoutines

/-- Both flat nodes and their framed master are produced and retained. The
flat list is copied before framing consumes it, and restored afterwards. -/
theorem nodesPhase_eval (a : Data) (t d Q W : ℕ) (ht : 0 < t)
    (hw : ∀ i,(a.stacks i).length ≤ W)
    (hzero : a.stacks 203=List.replicate (baseWidth 3 t) false)
    (hd : (a.stacks 204).length=d)
    (hq : BinaryArithmetic.toNat (a.stacks 361)=Q)
    (hcount : a.stacks 296=List.replicate Q true)
    (hwidth : (a.stacks 280).length=d*baseWidth 3 t) :
    ∃ n ≤ nodesBudget W t d Q, ∃ e : Data,
      Eval nodesPhase n a e ∧
      e.stacks 256=((nodeWords t d Q).map RingProgram.flat).flatten ∧
      e.stacks 300=Encoding.encodeList id ((nodeWords t d Q).map RingProgram.flat) ∧
      (∀ i, i∉296::nodesStartPorts → e.stacks i=a.stacks i) := by
  let a0 := clearedPorts nodesStartPorts a
  let a1 := copiedPlan nodeInputs a0
  have hc := clearPorts_eval nodesStartPorts a
  have h639 : a0.stacks 639=[] := by simp [a0,clearedPorts_stacks,nodesStartPorts]
  have hcopy := copyPlan_eval nodeInputs a0 (by
    intro p hp
    simp only [nodeInputs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl <;> decide) h639
  have ha1 (i : Fin 640) : a1.stacks i=
      Function.update (Function.update a0.stacks 617 (a0.stacks 203)) 625 (a0.stacks 361) i := by
    simp [a1,nodeInputs,copiedPlan,copied]
  have hin : NodesInput t a1 := by
    constructor
    · simpa [ha1,a0,clearedPorts_stacks,nodesStartPorts] using hzero
    · intro i hi
      fin_cases i <;> simp_all [a0,clearedPorts_stacks,nodesStartPorts,nodes]
  have hd1 : (a1.stacks 204).length=d := by
    simpa [ha1,a0,clearedPorts_stacks,nodesStartPorts] using hd
  have hq1 : BinaryArithmetic.toNat (a1.stacks 625)=Q := by
    simpa [ha1,a0,clearedPorts_stacks,nodesStartPorts] using hq
  have hl1 : (a1.stacks 625).length ≤ W := by
    simpa [ha1,a0,clearedPorts_stacks,nodesStartPorts] using hw 361
  obtain ⟨nn,hnn,a2,hnodes,hflat,hdeg,hframe⟩ := nodesCall_produces t ht a1 hin
  have hflat' : a2.stacks 256=((nodeWords t d Q).map RingProgram.flat).flatten := by
    cases hd1
    simpa only [hq1] using hflat
  have hlen : (a2.stacks 256).length=Q*(d*baseWidth 3 t) := by
    rw [hflat',nodeWords_flat_length]
  have h2frame (i : Fin 640) (hi : ¬∃ j,nodes j=i) :
      a2.stacks i=Function.update (Function.update a0.stacks 617 (a0.stacks 203))
        625 (a0.stacks 361) i := (hframe i hi).trans (ha1 i)
  have h628 : a2.stacks 628=[] := by
    rw [h2frame 628 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  have h2639 : a2.stacks 639=[] := by
    rw [h2frame 639 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  let a3 : Data := ⟨readRegs a2.regs 30 31 none,
    Function.update a2.stacks 628 (a2.stacks 256)⟩
  have hsave : Eval (overwrite 256 628) (7*(Q*(d*baseWidth 3 t))+8) a2 a3 := by
    simpa [a3,h628,hlen] using overwrite_eval 256 628 a2 (by decide) (by decide) (by decide) h2639
  have h3width : a3.stacks 280=a.stacks 280 := by
    simp only [a3,Function.update_of_ne (by decide : (280 : Fin 640)≠628)]
    rw [h2frame 280 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  have hf295 : a2.stacks 295=[] := by
    rw [h2frame 295 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  have hf297 : a2.stacks 297=[] := by
    rw [h2frame 297 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  have hf298 : a2.stacks 298=[] := by
    rw [h2frame 298 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  have hf299 : a2.stacks 299=[] := by
    rw [h2frame 299 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  have hf306 : a2.stacks 306=[] := by
    rw [h2frame 306 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  have hf300 : a2.stacks 300=[] := by
    rw [h2frame 300 (by decide)]
    simp [a0,clearedPorts_stacks,nodesStartPorts]
  have hf296 : a2.stacks 296=List.replicate Q true := by
    rw [h2frame 296 (by decide)]
    simpa [a0,clearedPorts_stacks,nodesStartPorts] using hcount
  have hfinput : projectState (registers 5 (by decide)) nodeFramePorts a3=
      SubexpTaylorFrames.state (a3.regs ∘ registers 5 (by decide))
        (SubexpTaylorFrames.data (a.stacks 280) Q
          (((nodeWords t d Q).map RingProgram.flat).flatten) []) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i
    · change a3.stacks 256 = _
      simpa [SubexpTaylorFrames.store, SubexpTaylorFrames.data, a3,
        Function.update_of_ne (by decide : (256 : Fin 640)≠628)] using hflat'
    · exact h3width
    · change a3.stacks 295 = _
      simpa [SubexpTaylorFrames.store, SubexpTaylorFrames.data, a3,
        Function.update_of_ne (by decide : (295 : Fin 640)≠628)] using hf295
    · change a3.stacks 296 = _
      simpa [SubexpTaylorFrames.store, SubexpTaylorFrames.data, a3,
        Function.update_of_ne (by decide : (296 : Fin 640)≠628)] using hf296
    · change a3.stacks 297 = _
      simpa [SubexpTaylorFrames.store, SubexpTaylorFrames.data, a3,
        Function.update_of_ne (by decide : (297 : Fin 640)≠628)] using hf297
    · change a3.stacks 298 = _
      simpa [SubexpTaylorFrames.store, SubexpTaylorFrames.data, a3,
        Function.update_of_ne (by decide : (298 : Fin 640)≠628)] using hf298
    · change a3.stacks 299 = _
      simpa [SubexpTaylorFrames.store, SubexpTaylorFrames.data, a3,
        Function.update_of_ne (by decide : (299 : Fin 640)≠628)] using hf299
    · change a3.stacks 306 = _
      simpa [SubexpTaylorFrames.store, SubexpTaylorFrames.data, a3,
        Function.update_of_ne (by decide : (306 : Fin 640)≠628)] using hf306
    · change a3.stacks 300 = _
      simpa [SubexpTaylorFrames.store, SubexpTaylorFrames.data, a3,
        Function.update_of_ne (by decide : (300 : Fin 640)≠628)] using hf300
  obtain ⟨rf,hfr⟩ := nodeFramesCall_eval a3 (a3.regs ∘ registers 5 (by decide))
    t d Q (a.stacks 280) hwidth hfinput
  let a4 := embedState (registers 5 (by decide)) nodeFramePorts a3
    (SubexpTaylorFrames.state rf
      {SubexpTaylorFrames.data (a.stacks 280) 0 [] [] with
        output:=Encoding.encodeList id ((nodeWords t d Q).map RingProgram.flat)})
  have h4256 : a4.stacks 256=[] := embedState_stack _ _ _ _ nodeFramePorts_injective 0
  have h4300 : a4.stacks 300=Encoding.encodeList id ((nodeWords t d Q).map RingProgram.flat) :=
    embedState_stack _ _ _ _ nodeFramePorts_injective 8
  have h4628 : a4.stacks 628=a2.stacks 256 := by
    rw [show a4.stacks 628=a3.stacks 628 from embedState_stack_frame _ _ _ _ _ (by decide)]
    simp [a3]
  have h4639 : a4.stacks 639=[] := by
    rw [show a4.stacks 639=a3.stacks 639 from embedState_stack_frame _ _ _ _ _ (by decide)]
    simpa [a3] using h2639
  let e : Data := ⟨readRegs a4.regs 30 31 none,Function.update a4.stacks 256 (a4.stacks 628)⟩
  have hrestore : Eval (overwrite 628 256) (7*(Q*(d*baseWidth 3 t))+8) a4 e := by
    simpa [e,h4256,h4628,hlen] using overwrite_eval 628 256 a4 (by decide) (by decide) (by decide) h4639
  have hcb := clearPortsCost_bound nodesStartPorts a W (fun i _ => hw i)
  have h0w : ∀ i,(a0.stacks i).length ≤ W := by
    intro i
    simp only [a0,clearedPorts_stacks]
    split_ifs <;> simp_all [hw i]
  have hpb := copyPlanCost_bound nodeInputs a0 W h0w
  have hnb : nn ≤ RingNodeProgram.budget (baseWidth 3 t) W d Q+5 := by
    rw [hd1,hq1] at hnn
    apply hnn.trans
    unfold RingNodeProgram.budget RingNodeProgram.stepBudget
    gcongr
  refine ⟨clearPortsCost nodesStartPorts a+copyPlanCost nodeInputs a0+nn+
      (7*(Q*(d*baseWidth 3 t))+8)+(Q*(28*(a.stacks 280).length+33)+11)+
      (7*(Q*(d*baseWidth 3 t))+8),?_,e,?_,?_,?_,?_⟩
  · unfold nodesBudget
    rw [hwidth]
    change copyPlanCost nodeInputs a0 ≤ 2*(9*W+8) at hpb
    omega
  · simpa only [nodesPhase,Nat.add_assoc] using
      hc.seq (hcopy.seq (hnodes.seq (hsave.seq (hfr.seq hrestore))))
  · simpa [e,h4628] using hflat'
  · simpa [e] using h4300
  · intro i hi
    by_cases hi280 : i=280
    · subst i
      have hp280 : a4.stacks 280=a.stacks 280 :=
        embedState_stack _ _ _ _ nodeFramePorts_injective 1
      simpa [e] using hp280
    have hni : i≠256 ∧ i≠628 ∧ i≠617 ∧ i≠625 := by
      refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> subst i <;> exact hi (by decide)
    have hnf : ¬∃ j,nodeFramePorts j=i := by
      rintro ⟨j,rfl⟩
      fin_cases j
      all_goals simp [nodeFramePorts, nodesStartPorts] at hi hi280
    by_cases hi204 : i=204
    · subst i
      simp only [e,Function.update_of_ne (by decide : (204 : Fin 640)≠256)]
      rw [show a4.stacks 204=a3.stacks 204 from embedState_stack_frame _ _ _ _ _ (by decide)]
      simpa [a3,ha1,a0,clearedPorts_stacks,nodesStartPorts] using hdeg
    · have hnn' : ¬∃ j,nodes j=i := by
        rintro ⟨j,hj⟩
        by_cases hj14 : j=14
        · subst j
          exact hi204 hj.symm
        · have hm : nodes j∈296::nodesStartPorts := by
            fin_cases j
            all_goals simp [nodes, nodesStartPorts] at hj14 ⊢
          exact hi (hj ▸ hm)
      simp only [e,Function.update_of_ne hni.1]
      have ha4frame : a4.stacks i=a3.stacks i :=
        embedState_stack_frame _ _ _ _ _ hnf
      rw [ha4frame]
      simp only [a3,Function.update_of_ne hni.2.1]
      rw [h2frame i hnn']
      simp [hni.2.2.1,hni.2.2.2,a0,clearedPorts_stacks,
        show i∉nodesStartPorts from fun hh => hi (List.mem_cons_of_mem _ hh)]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

/-- The dynamic constant constructor emits the model's exact zero code. -/
theorem RingCaches.fullZero_model {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {u : RingProgram.ScalarCode 3 t} {a : Data}
    (h : RingCaches t d model M cache u a) :
    a.stacks 280=RingProgram.flat (RingProgram.modelProgram t model M cache).zeroRun.1 := by
  rw [h.fullZero,←LeafProgram.Constants.constantCode_flat]
  congr 1
  funext i
  simp [LeafProgram.Constants.constantCode,RingProgram.modelProgram,RingProgram.quotientProgram,
    RingProgram.program,RingProgram.zeroVector,RingProgram.scalarProgram]

/-- The dynamic constant constructor also emits the exact model one code. -/
theorem RingCaches.fullOne_model {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {u : RingProgram.ScalarCode 3 t} {a : Data}
    (h : RingCaches t d model M cache u a) :
    a.stacks 207=RingProgram.flat (RingProgram.modelProgram t model M cache).oneRun.1 := by
  rw [h.fullOne,←LeafProgram.Constants.constantCode_flat]
  congr 1
  funext i
  simp [LeafProgram.Constants.constantCode,RingProgram.modelProgram,RingProgram.quotientProgram,
    RingProgram.program,RingProgram.oneVectorRun,RingProgram.tabulateRun_eq,RingProgram.scalarProgram]
  split_ifs <;> rfl

theorem RingCaches.frame {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {u : RingProgram.ScalarCode 3 t} {a e : Data}
    (h : RingCaches t d model M cache u a)
    (hf : ∀ i∈ringCachePorts,e.stacks i=a.stacks i) : RingCaches t d model M cache u e := by
  constructor
  · simpa only [hf 194 (by decide)] using h.modulus
  · simpa only [hf 202 (by decide)] using h.width
  · simpa only [hf 204 (by decide)] using h.degree
  · simpa only [hf 203 (by decide)] using h.scalarZero
  · simpa only [hf 201 (by decide)] using h.table
  · simpa only [hf 212 (by decide)] using h.precision
  · simpa only [hf 253 (by decide)] using h.half
  · exact h.inverse
  · exact h.canonical
  · simpa only [hf 280 (by decide)] using h.fullZero
  · simpa only [hf 207 (by decide)] using h.fullOne
  · simpa only [hf 211 (by decide)] using h.fullMinusOne
  · simpa only [hf 190 (by decide), hf 280 (by decide)] using h.readoutZero
  · simpa only [hf 249 (by decide), hf 280 (by decide)] using h.aliasZero
  · simpa only [hf 250 (by decide), hf 207 (by decide)] using h.aliasOne
  · simpa only [hf 251 (by decide), hf 211 (by decide)] using h.aliasMinusOne

theorem constantsPhase_produces {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {u : RingProgram.ScalarCode 3 t} (a : Data) (h : CoreOutput t d model M cache u a)
    (W : ℕ) (hw : ∀ i,(a.stacks i).length ≤ W) :
    ∃ n ≤ constantsBudget W (baseWidth 3 t) d, ∃ e : Data,
      Eval constantsPhase n a e ∧ RingCaches t d model M cache u e ∧
      (∀ i, i∉constantStartPorts ∧ i∉([190,249,250,251] : List (Fin 640)) →
        e.stacks i=a.stacks i) := by
  obtain ⟨n,hn,e,he,hs⟩ := constantsPhase_eval a cache.one cache.minusOne cache.zero W hw
    h.one h.minusOne h.zero
  have hcalc (i : Fin 640) : e.stacks i=constantResultStacks a cache.one cache.minusOne cache.zero i :=
    congrFun hs i
  have hf (i : Fin 640) (hi : i∉constantStartPorts)
      (hj : i∉([190,249,250,251] : List (Fin 640))) : e.stacks i=a.stacks i := by
    rw [hcalc]
    unfold constantResultStacks
    rw [copiedPlan_frame]
    · have h207 : i≠207 := by intro hh; subst i; exact hi (by decide)
      have h211 : i≠211 := by intro hh; subst i; exact hi (by decide)
      have h280 : i≠280 := by intro hh; subst i; exact hi (by decide)
      have h538 : i≠538 := by intro hh; subst i; exact hi (by decide)
      simp [constantBatchStacks,h207,h211,h280,h538,clearedPorts_stacks,hi]
    · intro p hp
      simp only [constantAliases,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl <;> intro hh <;> subst i <;> exact hj (by simp)
  have hspecial (i : Fin 640) := congrFun hs i
  have h204 : (clearedPorts constantStartPorts a).stacks 204=a.stacks 204 := by
    rw [clearedPorts_stacks,ite_eq_right (by decide)]
  refine ⟨n,by simpa [h.degree] using hn,e,he,?_,fun i hi => hf i hi.1 hi.2⟩
  constructor
  · simpa only [hf 194 (by decide) (by decide)] using h.modulus
  · simpa only [hf 202 (by decide) (by decide)] using h.width
  · simpa only [hf 204 (by decide) (by decide)] using h.degree
  · simpa only [hf 203 (by decide) (by decide)] using h.zero
  · simpa only [hf 201 (by decide) (by decide)] using h.table
  · simpa only [hf 212 (by decide) (by decide)] using h.precision
  · simpa only [hf 253 (by decide) (by decide)] using h.half
  · exact h.inverse
  · exact h.zeroCanonical
  all_goals simp [hcalc,constantResultStacks,constantAliases,copiedPlan,copied,
    constantBatchStacks,h204,h.degree]

theorem finalCleanup_produces {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {u : RingProgram.ScalarCode 3 t} (a : Data) (h : RingCaches t d model M cache u a) :
    ∃ e : Data, Eval finalCleanup (clearPortsCost finalDiscard a+32) a e ∧
      RingCaches t d model M cache u e ∧ NativeBytes t d model M cache e ∧
      (∀ i∈privatePorts,e.stacks i=[]) ∧
      (∀ i, i∉finalDiscard → e.stacks i=a.stacks i) := by
  let a0 := clearedPorts finalDiscard a
  let e := RegisterResetProgram.zeroed a0
  have hf (i : Fin 640) (hi : i∉finalDiscard) : e.stacks i=a.stacks i := by
    simp [e,a0,clearedPorts_stacks,hi]
  have hr : RingCaches t d model M cache u e := h.frame (by
    intro i hi
    apply hf
    simp only [ringCachePorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
  refine ⟨e,(clearPorts_eval finalDiscard a).seq (RegisterResetProgram.all_eval a0),hr,?_,?_,hf⟩
  · refine ⟨hr.modulus,hr.width,hr.scalarZero,hr.table,hr.degree,?_,?_⟩
    · rw [hr.fullZero,←LeafProgram.Constants.constantCode_flat,RingProgram.flat_length]
    · intro i hi
      have hm : i.castLE (by decide)∈finalDiscard := by
        apply List.mem_append_right
        apply List.mem_map.mpr
        exact ⟨i,List.mem_append_left _ hi,rfl⟩
      simp [e,a0,clearedPorts_stacks,hm]
  · intro i hi
    have hm : i∈finalDiscard := List.mem_append_left _ (List.mem_cons_of_mem _ hi)
    simp [e,a0,clearedPorts_stacks,hm]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def earlyCall : Code := .call (ProgramLinking.liftProgram EarlyThreshold.program r8 early)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendHighRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The high mask is computed from the original ambient count and actual scope
mass. The forward mask is a paid copy/reversal of that same output. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


def highCommand : Code := sequence [copy 709 417,earlyCall,copies highCopies,
  highCall,copy 594 338,maskCall]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendPost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid persistent metadata export, offset construction, mask conversion, and
scratch cleanup after the guarded numeric bank has been computed. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


abbrev Exported (m : Circuit.Model) (a : Data) : Prop :=
  (∀ i : Fin 8, a.stacks (Exports.destination (i.castAdd 8))=
    List.replicate (Exports.unaryValues m i) true) ∧
  (∀ i : Fin 8, BinaryArithmetic.toNat (a.stacks (Exports.destination (i.natAdd 8)))=
    m.val (Exports.binarySources i))

def postCommand : Code := .seq Exports.prepareCommand
  (.seq offsetCall (.seq lowMask clearPrivate))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Empty (a : Wide.Data) : Prop where
  bank : Wide.BankEmpty (Wide.project a)
  temporary : a.stacks 684=[]
  words : a.stacks 133=[]
  metadata : a.stacks 135=[]
  plans : a.stacks 136=[]
  parked : ∀ i,a.stacks (LeafProgram.LayoutMasters.high i)=[]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramPreparedSpec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A typed factor specification using the original query's row stream and
marked-clause selector. Finite-index transports do not alter stored bytes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics MomentsProgram
noncomputable section

theorem origin_good {r Q n d : ℕ} (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (hu : 0 < u) (hJ : 0 < J) :
    Good Finset.univ u J (NodeNative.originEntries (n:=n) p.ops.oneRun.1) :=
  FactorBounds.indicator_good_iff.mp (NodeNative.originEntries_valid _ _ u J hu hJ)

theorem origin_value {r Q n d : ℕ} (p : SourceBank.Parameters r Q d) (u J : ℕ)
    (hu : 0 < u) (hJ : 0 < J) :
    rawDenote p.ops.decode (NodeNative.originEntries (n:=n) p.ops.oneRun.1)=Squarefree.canonical u J 1 := by
  have h := Squarefree.Sparse.denote_one (V:=Fin n) (R:=p.model.O p.t) u J
  simpa only [Squarefree.Sparse.one,Squarefree.Sparse.constant,hu,hJ,and_self,ite_true, if_true,
    rawDenote,NodeNative.originEntries,Dictionary.denoteTable,List.map_cons,List.map_nil,p.ops.one_correct] using h

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

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

theorem number (i : Fin 640) (hi : i.val < 190) : EmptyPreserved numberPhase i := by
  unfold numberPhase
  have hs : EmptyPreserved serializationCall i := by
    apply highLift _ _ _ i hi
    intro j
    change 190 ≤ 340+j.val
    omega
  have hu : EmptyPreserved (LeafRingSetupProgram.unaryPlan numericPlan) i :=
    unaryPlan numericPlan i hi (by
      intro p hp
      simp only [numericPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide)
  exact seq (clearPorts _ i) (seq hs (seq hu (seq
    (overwrite 373 511 i hi (by decide) (by decide)) (resetAll i))))

theorem core (i : Fin 640) (hi : i.val < 190) : EmptyPreserved coreCommand i := by
  unfold coreCommand searchAndPad
  have hs : ∀ j,190 ≤ (scalar j).val := by intro j; unfold scalar; split_ifs <;> (try dsimp only) <;> omega
  have hh : ∀ j,190 ≤ (search j).val := by intro j; unfold search; split_ifs <;> (try dsimp only) <;> omega
  have ht : ∀ j,190 ≤ (table j).val := by intro j; unfold table; split_ifs <;> (try dsimp only) <;> omega
  have sc : EmptyPreserved scalarCall i := highLift _ _ _ i hi hs
  have se : EmptyPreserved searchCall i := highLift _ _ _ i hi hh
  have pa : EmptyPreserved paddingCall i := highLift _ _ _ i hi hh
  have ta : EmptyPreserved tableCall i := highLift _ _ _ i hi ht
  exact seq sc (seq (overwrite 507 253 i hi (by decide) (by decide)) (seq (resetAll i)
    (seq (seq se (seq (overwrite 202 432 i hi (by decide) (by decide)) pa))
      (seq (overwrite 498 538 i hi (by decide) (by decide)) ta))))

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.LowFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ring and interpolation setup are performed once per marked query. All
arithmetic objects in the conclusion are generated by the two native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
open LeafRingSetupProgram

def budget (m : Circuit.Model) (W V L : ℕ) : ℕ :=
  let B := producerBudget m W V L+1
  B+10000*(W+B+1+InterpolationCacheProgram.budget (m.val 33) (m.val 34) (m.val 21)+2)

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Ring

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual arithmetic preparation per query: ring caches, interpolation
caches, then the inverse layout denominator. All three run before branching. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

 def arithmeticBudget (m : Circuit.Model) (W V L R : ℕ) : ℕ :=
  Ring.budget m W V L+
    LayoutDenominatorProgramQuery.budget R (m.val 33) (m.val 34) (W+Ring.budget m W V L+1)

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end


